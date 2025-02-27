use {
    assert_cmd::{output::OutputOkExt, Command},
    std::{ffi::OsStr, path::Path},
};

#[test]
fn format_problem_files_for_strong_equivalence_examples() {
    for example in Path::new(file!())
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("res/examples/strong_equivalence")
        .read_dir()
        .unwrap()
        .map(Result::unwrap)
        .filter(|entry| entry.metadata().unwrap().is_dir())
        .map(|entry| entry.path())
    {
        let dir = example
            .clone()
            .components()
            .last()
            .unwrap()
            .as_os_str()
            .to_str()
            .unwrap()
            .to_string();
        let p1 = example.join(format!("{dir}.1.lp"));
        let p2 = example.join(format!("{dir}.2.lp"));

        let mut cmd = Command::cargo_bin(env!("CARGO_PKG_NAME")).unwrap();
        let generate_problem_files = cmd
            .arg("verify")
            .arg("--equivalence")
            .arg("strong")
            .arg(p1)
            .arg(p2)
            .arg("--no-proof-search")
            .arg("--save-problems")
            .arg("./tests/formatting/tptp/out");
        let _output = generate_problem_files.unwrap();

        for file in Path::new(file!())
            .parent()
            .unwrap()
            .join("out")
            .read_dir()
            .unwrap()
            .map(Result::unwrap)
            .filter(|entry| entry.metadata().unwrap().is_file())
            .map(|entry| entry.path())
            .filter(|file| {
                let _dotp = OsStr::new("p");
                matches!(file.extension(), Some(_dotp))
            })
        {
            let problem_file = file.as_os_str().to_str().unwrap();
            let mut cmd = std::process::Command::new("./tests/formatting/tptp/out/tptp4X");

            let _output = cmd.arg(problem_file).unwrap();

            // match output.status.code() {
            //     Some(code) => assert_eq!(code, 0),
            //     None => assert!(false),
            // }

            // let mut cmd = std::process::Command::new("rm");
            // cmd.arg("./tests/formatting/tptp/out/forward_*").unwrap();
        }
    }
}
