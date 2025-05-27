use {
    crate::{
        analyzing::{regularity::Regularity as _, tightness::Tightness},
        command_line::{
            arguments::{
                Arguments, Command, Equivalence, Output, ParseAs, Property,
                SimplificationPortfolio, SimplificationStrategy, Translation,
            },
            files::Files,
        },
        convenience::{apply::Apply, compose::Compose},
        simplifying::fol::{classic::CLASSIC, ht::HT, intuitionistic::INTUITIONISTIC},
        syntax_tree::{
            Node as _, asp,
            fol::{self, Theory},
            superasp,
        },
        translating::{
            alpha::alpha, completion::completion_with_axioms, counting::TargetTheory, gamma::gamma,
            mu::mu, natural::natural, tau_star::tau_star_with_axioms,
        },
        verifying::{
            prover::{Prover, Report, Status, Success, vampire::Vampire},
            task::{
                Task, external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::StrongEquivalenceTask,
            },
        },
    },
    anyhow::{Context, Result, anyhow},
    clap::Parser as _,
    either::Either,
    std::time::Instant,
};

pub fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Analyze { property, input } => {
            match property {
                Property::Regularity => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let is_regular = program.is_regular();
                    println!("{is_regular}");
                }

                Property::Tightness => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let is_tight = program.is_tight();
                    println!("{is_tight}");
                }
            }

            Ok(())
        }

        Command::Parse {
            r#as,
            output,
            input,
        } => {
            match r#as {
                ParseAs::Program => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    match output {
                        Output::Debug => println!("{program:#?}"),
                        Output::Default => print!("{program}"),
                    }
                }
                ParseAs::Theory => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    match output {
                        Output::Debug => println!("{theory:#?}"),
                        Output::Default => print!("{theory}"),
                    }
                }
                ParseAs::Specification => {
                    let specification = input.map_or_else(
                        fol::Specification::from_stdin,
                        fol::Specification::from_file,
                    )?;
                    match output {
                        Output::Debug => println!("{specification:#?}"),
                        Output::Default => print!("{specification}"),
                    }
                }
                ParseAs::UserGuide => {
                    let user_guide =
                        input.map_or_else(fol::UserGuide::from_stdin, fol::UserGuide::from_file)?;
                    match output {
                        Output::Debug => println!("{user_guide:#?}"),
                        Output::Default => print!("{user_guide}"),
                    }
                }
            };

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

        Command::Translate {
            with,
            include_axioms,
            no_simplify,
            input,
        } => {
            match with {
                Translation::Completion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;

                    let target_theory = TargetTheory {
                        formulas: theory.formulas,
                        axioms: vec![],
                    };

                    let completed_theory = completion_with_axioms(target_theory)
                        .context("the given theory is not completable")?;

                    let mut completion = Theory::from_iter(completed_theory.formulas);

                    if !no_simplify {
                        let mut portfolio =
                            [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
                        completion = completion
                            .into_iter()
                            .map(|formula| formula.apply_fixpoint(&mut portfolio))
                            .collect();
                    }

                    if include_axioms {
                        println!("\tSupporting Axioms:");
                        let mut axioms = Theory::from_iter(completed_theory.axioms);
                        if !no_simplify {
                            let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
                            axioms = axioms
                                .into_iter()
                                .map(|formula| formula.apply_fixpoint(&mut portfolio))
                                .collect();
                        }
                        print!("{axioms}");
                        println!("\tcompletion:");
                    }

                    print!("{completion}")
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let mut gamma_theory = gamma(theory);
                    if !no_simplify {
                        let mut portfolio =
                            [INTUITIONISTIC, HT, CLASSIC].concat().into_iter().compose();
                        gamma_theory = gamma_theory
                            .into_iter()
                            .map(|formula| formula.apply_fixpoint(&mut portfolio))
                            .collect();
                    }
                    print!("{gamma_theory}")
                }

                Translation::Mu => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let mut theory = mu(program);
                    if !no_simplify {
                        let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
                        theory = theory
                            .into_iter()
                            .map(|formula| formula.apply_fixpoint(&mut portfolio))
                            .collect();
                    }
                    print!("{theory}")
                }

                Translation::Natural => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let mut theory =
                        natural(program).context("the given program is not regular")?;
                    if !no_simplify {
                        let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
                        theory = theory
                            .into_iter()
                            .map(|formula| formula.apply_fixpoint(&mut portfolio))
                            .collect();
                    }
                    print!("{theory}")
                }

                Translation::TauStar => {
                    let program = input
                        .map_or_else(superasp::Program::from_stdin, superasp::Program::from_file)?;

                    let reduced_program = alpha(program)?;

                    let theory = tau_star_with_axioms(reduced_program, None);
                    let mut taustar = Theory::from_iter(theory.formulas);

                    if !no_simplify {
                        let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
                        taustar = taustar
                            .into_iter()
                            .map(|formula| formula.apply_fixpoint(&mut portfolio))
                            .collect();
                    }

                    if include_axioms {
                        println!("\tSupporting Axioms:");
                        let mut axioms = Theory::from_iter(theory.axioms);
                        if !no_simplify {
                            let mut portfolio = [INTUITIONISTIC, HT].concat().into_iter().compose();
                            axioms = axioms
                                .into_iter()
                                .map(|formula| formula.apply_fixpoint(&mut portfolio))
                                .collect();
                        }
                        print!("{axioms}");
                        println!("\ttau-star:");
                    }

                    print!("{taustar}");
                }
            }

            Ok(())
        }

        Command::Verify {
            equivalence,
            decomposition,
            direction,
            formula_representation,
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
                Equivalence::Strong => {
                    let left_program = superasp::Program::from_file(
                        files
                            .left()
                            .ok_or(anyhow!("no left program was provided"))?,
                    )?;

                    let right_program = superasp::Program::from_file(
                        files
                            .right()
                            .ok_or(anyhow!("no right program was provided"))?,
                    )?;

                    StrongEquivalenceTask {
                        left: alpha(left_program)?,
                        right: alpha(right_program)?,
                        proof_outline: files
                            .proof_outline()
                            .map(fol::Specification::from_file)
                            .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                        decomposition,
                        formula_representation,
                        direction,
                        simplify: !no_simplify,
                        break_equivalences: !no_eq_break,
                    }
                    .decompose()?
                    .report_warnings()
                }

                Equivalence::External => ExternalEquivalenceTask {
                    specification: match files
                        .specification()
                        .ok_or(anyhow!("no specification was provided"))?
                    {
                        Either::Left(program) => {
                            let spec = superasp::Program::from_file(program)?;
                            Either::Left(alpha(spec)?)
                        }
                        Either::Right(specification) => {
                            Either::Right(fol::Specification::from_file(specification)?)
                        }
                    },
                    program: {
                        let program = superasp::Program::from_file(
                            files.program().ok_or(anyhow!("no program was provided"))?,
                        )?;
                        alpha(program)?
                    },
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
                    formula_representation,
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
                    print!("> Success! Anthem found a proof of the theorem.")
                } else {
                    print!("> Failure! Anthem was unable to find a proof of the theorem.")
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
