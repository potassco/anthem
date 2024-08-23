use {
    crate::{
        analyzing::tightness::Tightness,
        command_line::{
            arguments::{Arguments, Command, Equivalence, Property, Translation},
            files::Files,
        },
        syntax_tree::{asp, fol, Node as _},
        translating::{completion::completion, gamma::gamma, tau_star::tau_star},
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
            time_limit,
            save_problems: out_dir,
            files,
        } => {
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
                let mut success = true;
                for problem in problems {
                    // TODO: Handle the error cases properly
                    let report = Vampire { time_limit }.prove(problem)?;
                    if !matches!(report.status()?, Status::Success(Success::Theorem)) {
                        success = false;
                    }
                    println!("{report}");
                }

                println!("--- Summary ---");
                if success {
                    println!("Success! Anthem found a proof of equivalence.");
                } else {
                    println!("Failure! Anthem was unable to find a proof of equivalence.");
                }
            }

            Ok(())
        }
    }
}
