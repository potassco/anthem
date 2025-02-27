use {
    crate::{
        analyzing::tightness::Tightness,
        command_line::{
            arguments::{
                Arguments, Command, Equivalence, Property, SimplificationPortfolio,
                SimplificationStrategy, Translation,
            },
            files::Files,
        },
        convenience::{apply::Apply, compose::Compose},
        simplifying::fol::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{asp, fol, Node as _},
        translating::{
            completion::completion, gamma::gamma, ordered_completion::ordered_completion,
            tau_star::tau_star,
        },
        verifying::{
            prover::{vampire::Vampire, Prover, Report, Status, Success},
            task::{
                external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::StrongEquivalenceTask, Task,
            },
        },
    },
    anyhow::{anyhow, Context, Result},
    clap::Parser as _,
    either::Either,
    std::time::Instant,
};

pub fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Analyze { property, input } => {
            match property {
                Property::Tightness => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let is_tight = program.is_tight();
                    println!("{is_tight}");
                }
            }

            Ok(())
        }

        Command::Simplify {
            portfolio,
            strategy,
            input,
        } => {
            let mut simplification = match portfolio {
                SimplificationPortfolio::Classic => [INTUITIONISTIC, HT, CLASSIC].concat(),
                SimplificationPortfolio::Ht => [INTUITIONISTIC, HT].concat(),
                SimplificationPortfolio::Intuitionistic => [INTUITIONISTIC].concat(),
            }
            .into_iter()
            .compose();

            let theory = input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;

            let simplified_theory: fol::Theory = theory
                .into_iter()
                .map(|formula| match strategy {
                    SimplificationStrategy::Shallow => simplification(formula),
                    SimplificationStrategy::Recursive => formula.apply(&mut simplification),
                    SimplificationStrategy::Fixpoint => formula.apply_fixpoint(&mut simplification),
                })
                .collect();

            print!("{simplified_theory}");

            Ok(())
        }

        Command::Translate { with, input } => {
            match with {
                Translation::Completion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let completed_theory =
                        completion(theory).context("the given theory is not completable")?;
                    print!("{completed_theory}")
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let gamma_theory = gamma(theory);
                    print!("{gamma_theory}")
                }

                Translation::OrderedCompletion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let ordered_completion_theory = ordered_completion(theory)
                        .context("the given theory is not completable")?;
                    print!("{ordered_completion_theory}")
                }

                Translation::TauStar => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let theory = tau_star(program);
                    print!("{theory}")
                }
            }

            Ok(())
        }

        Command::Verify {
            equivalence,
            decomposition,
            direction,
            bypass_tightness,
            no_simplify,
            no_eq_break,
            no_proof_search,
            no_timing,
            time_limit,
            prover_instances,
            prover_cores,
            save_problems: out_dir,
            files,
        } => {
            let start_time = Instant::now();

            let files =
                Files::sort(files).context("unable to sort the given files by their function")?;

            let problems = match equivalence {
                Equivalence::Strong => StrongEquivalenceTask {
                    left: asp::Program::from_file(
                        files
                            .left()
                            .ok_or(anyhow!("no left program was provided"))?,
                    )?,
                    right: asp::Program::from_file(
                        files
                            .right()
                            .ok_or(anyhow!("no right program was provided"))?,
                    )?,
                    decomposition,
                    direction,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
                Equivalence::External => ExternalEquivalenceTask {
                    specification: match files
                        .specification()
                        .ok_or(anyhow!("no specification was provided"))?
                    {
                        Either::Left(program) => Either::Left(asp::Program::from_file(program)?),
                        Either::Right(specification) => {
                            Either::Right(fol::Specification::from_file(specification)?)
                        }
                    },
                    program: asp::Program::from_file(
                        files.program().ok_or(anyhow!("no program was provided"))?,
                    )?,
                    user_guide: fol::UserGuide::from_file(
                        files
                            .user_guide()
                            .ok_or(anyhow!("no user guide was provided"))?,
                    )?,
                    proof_outline: files
                        .proof_outline()
                        .map(fol::Specification::from_file)
                        .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                    decomposition,
                    direction,
                    bypass_tightness,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
            };

            if let Some(out_dir) = out_dir {
                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    time_limit,
                    instances: prover_instances,
                    cores: prover_cores,
                };

                let problems = problems.into_iter().inspect(|problem| {
                    println!("> Proving {}...", problem.name);
                    println!("Axioms:");
                    for axiom in problem.axioms() {
                        println!("    {}", axiom.formula);
                    }
                    println!();
                    println!("Conjectures:");
                    for conjecture in problem.conjectures() {
                        println!("    {}", conjecture.formula);
                    }
                    println!();
                });

                let mut success = true;
                for result in prover.prove_all(problems) {
                    match result {
                        Ok(report) => match report.status() {
                            Ok(status) => {
                                println!(
                                    "> Proving {} ended with a SZS status",
                                    report.problem.name
                                );
                                print!("Status: {status}");
                                if !no_timing {
                                    print!(" ({} ms)", report.elapsed_time.as_millis())
                                }
                                println!();
                                if !matches!(status, Status::Success(Success::Theorem)) {
                                    success = false;
                                }
                            }
                            Err(error) => {
                                println!(
                                    "> Proving {} ended without a SZS status",
                                    report.problem.name
                                );
                                println!("Output/stdout:");
                                println!("{}", report.output.stdout);
                                println!("Output/stderr:");
                                println!("{}", report.output.stderr);
                                println!("Error: {error}");
                                success = false;
                            }
                        },
                        Err(error) => {
                            println!("> Proving <a problem> ended with an error"); // TODO: Get the name of the problem
                            println!("Error: {error}");
                            success = false;
                        }
                    }
                    println!();
                }

                if success {
                    print!("> Success! Anthem found a proof of equivalence.")
                } else {
                    print!("> Failure! Anthem was unable to find a proof of equivalence.")
                }

                if !no_timing {
                    print!(" ({} ms)", start_time.elapsed().as_millis())
                }

                println!()
            }

            Ok(())
        }
    }
}
