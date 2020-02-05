from pathlib import Path
import sys
import subprocess


class TestRunner:
    def __init__(self):
        self.passed = 0
        self.failed = 0

    def run(self, test_file, expected_file):
        run_result = compile_and_run(test_file)

        with expected_file.open("r") as f:
            expect = f.read()

        if run_result == expect:
            self.passed += 1
            print("test {} ... ok".format(path))
        else:
            self.failed += 1
            print("test {} ... FAILED".format(path))

    def print_stat(self):
        if self.failed == 0:
            total_result = "ok"
        else:
            total_result = "FAILED"

        print(
            "\ntest result: {}. {} passed; {} failed; 0 ignored; 0 measured; 0 filtered out".format(
                total_result,
                self.passed,
                self.failed))

    def all_passed(self):
        return self.failed == 0


def compile_and_run(test_file):
    subprocess.run(["cargo", "run", test_file, "-otmp.out"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    result = subprocess.check_output(["tmp.out"])
    return result.decode("utf-8")


TARGET_DIR = Path("./tigerc/tests")
runner = TestRunner()

for path in TARGET_DIR.glob("*.tig"):
    stem = path.stem
    expect_path = path.parent / (stem + ".expect")
    runner.run(path, expect_path)

runner.print_stat()

if not runner.all_passed():
    sys.exit(101)
