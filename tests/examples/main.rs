use {
    assert_cmd::Command,
    std::{
        fs::File,
        io::{BufRead, BufReader},
        path::{Path, PathBuf},
    },
    tempfile::tempdir,
    walkdir::WalkDir,
};

struct Test {
    directory: PathBuf,
    name: String,
    arguments: Vec<String>,
}

impl Test {
    fn find() -> impl Iterator<Item = Self> {
        WalkDir::new(Path::new(env!("CARGO_MANIFEST_DIR")).join("res/examples"))
            .into_iter()
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_file())
            .filter(|entry| entry.file_name().to_str().unwrap_or_default() == ".tests")
            .flat_map(|entry| {
                File::open(entry.path())
                    .into_iter()
                    .map(BufReader::new)
                    .flat_map(BufRead::lines)
                    .filter_map(Result::ok)
                    .map(move |line| {
                        let mut parts = line.split_whitespace();
                        Self {
                            directory: entry.path().parent().unwrap().to_path_buf(),
                            name: parts.next().unwrap_or_default().to_string(),
                            arguments: parts.map(String::from).collect(),
                        }
                    })
            })
    }

    fn execute(&self) {
        match self.name.as_str() {
            "tptp_compliance" => {
                let out = tempdir().unwrap().into_path();

                Command::cargo_bin(env!("CARGO_PKG_NAME"))
                    .unwrap()
                    .current_dir(&self.directory)
                    .args(
                        self.arguments
                            .iter()
                            .map(|argument| match argument.as_str() {
                                "$OUT" => out.to_str().unwrap(),
                                _ => argument,
                            }),
                    )
                    .assert()
                    .success();

                WalkDir::new(out)
                    .into_iter()
                    .filter_map(Result::ok)
                    .filter(|entry| entry.file_type().is_file())
                    .for_each(|entry| {
                        Command::new(Path::new(file!()).parent().unwrap().join("tptp4X"))
                            .arg(entry.path())
                            .assert()
                            .success();
                    });
            }

            _ => panic!("unknown test: {}", self.name),
        }
    }
}

#[test]
fn verify() {
    for test in Test::find() {
        test.execute()
    }
}
