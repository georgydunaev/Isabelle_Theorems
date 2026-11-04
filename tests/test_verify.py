import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import verify


class TestIsabelleTheorems(unittest.TestCase):
    def test_all_thy_files_valid(self):
        self.assertEqual(verify.main(), 0)


if __name__ == "__main__":
    unittest.main()
