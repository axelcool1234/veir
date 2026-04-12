window.BENCHMARK_DATA = {
  "lastUpdate": 1775981645820,
  "repoUrl": "https://github.com/axelcool1234/veir",
  "entries": {
    "VeIR Benchmarks": [
      {
        "commit": {
          "author": {
            "email": "tobias@grosser.es",
            "name": "Tobias Grosser",
            "username": "tobiasgrosser"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f265cbe909287e67c0b024e14d09c8483cd44e56",
          "message": "Add back maxHeartbeats to avoid timeout (#399)",
          "timestamp": "2026-04-11T19:00:21Z",
          "tree_id": "8a05496ab95648225ac17ab93c7989d67e5f7f1d",
          "url": "https://github.com/axelcool1234/veir/commit/f265cbe909287e67c0b024e14d09c8483cd44e56"
        },
        "date": 1775981645478,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "add-fold-worklist/create",
            "value": 2474000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002474s"
          },
          {
            "name": "add-fold-worklist/rewrite",
            "value": 3656000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003656s"
          },
          {
            "name": "add-fold-worklist-local/create",
            "value": 2196000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002196s"
          },
          {
            "name": "add-fold-worklist-local/rewrite",
            "value": 3090000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003090s"
          },
          {
            "name": "add-zero-worklist/create",
            "value": 2092000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002092s"
          },
          {
            "name": "add-zero-worklist/rewrite",
            "value": 2409000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002409s"
          },
          {
            "name": "add-zero-reuse-worklist/create",
            "value": 1893000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001893s"
          },
          {
            "name": "add-zero-reuse-worklist/rewrite",
            "value": 1946000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001946s"
          },
          {
            "name": "mul-two-worklist/create",
            "value": 2225000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002225s"
          },
          {
            "name": "mul-two-worklist/rewrite",
            "value": 5380000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.005380s"
          },
          {
            "name": "add-fold-forwards/create",
            "value": 2186000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002186s"
          },
          {
            "name": "add-fold-forwards/rewrite",
            "value": 2959000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.002959s"
          },
          {
            "name": "add-zero-forwards/create",
            "value": 2268000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002268s"
          },
          {
            "name": "add-zero-forwards/rewrite",
            "value": 1959000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001959s"
          },
          {
            "name": "add-zero-reuse-forwards/create",
            "value": 1696000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001696s"
          },
          {
            "name": "add-zero-reuse-forwards/rewrite",
            "value": 1509000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.001509s"
          },
          {
            "name": "mul-two-forwards/create",
            "value": 2109000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.002109s"
          },
          {
            "name": "mul-two-forwards/rewrite",
            "value": 3586000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.003586s"
          },
          {
            "name": "add-zero-reuse-first/create",
            "value": 1699000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001699s"
          },
          {
            "name": "add-zero-reuse-first/rewrite",
            "value": 8000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000008s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/create",
            "value": 1908000,
            "unit": "ns",
            "extra": "count=1000 pc=100 create=0.001908s"
          },
          {
            "name": "add-zero-lots-of-reuse-first/rewrite",
            "value": 751000,
            "unit": "ns",
            "extra": "count=1000 pc=100 rewrite=0.000751s"
          }
        ]
      }
    ]
  }
}