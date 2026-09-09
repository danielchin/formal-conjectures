# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0.
import tempfile
from pathlib import Path
import unittest
from ci_shards import partition


class PartitionTest(unittest.TestCase):
    def test_complete_disjoint_and_deterministic(self):
        with tempfile.TemporaryDirectory() as d:
            files = []
            for index, size in enumerate([400, 200, 80, 40, 20, 10, 10, 10]):
                p = Path(d) / f"{index}.lean"
                p.write_text("x" * size)
                files.append(p)
            groups = partition(files, 4)
            flat = [p for group in groups for p in group]
            self.assertCountEqual(flat, files)
            self.assertEqual(len(flat), len(set(flat)))
            self.assertEqual(groups, partition(reversed(files), 4))
            self.assertTrue(all(groups))
            self.assertEqual(groups[0], [files[0]])

    def test_invalid_count(self):
        with self.assertRaises(ValueError):
            partition([], 0)

    def test_single_shard(self):
        files = list(Path("FormalConjectures").rglob("*.lean"))
        self.assertEqual(partition(files, 1), [sorted(files)])


if __name__ == "__main__":
    unittest.main()
