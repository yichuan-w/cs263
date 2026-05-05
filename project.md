# CS 263 Project Proposal

**Authors:** Yichuan Wang, Qiuyang Mang

## Project Title

Automated Test Oracles Discovery for Database Management Systems via Lean

## Introduction and Background

Database Management Systems (DBMS) are a critical infrastructure, yet logic bugs within them can silently return incorrect query results, leading to significant issues for downstream applications. Existing DBMS testing solutions have primarily relied on manual test case creation or reference engines, but more recently, on the concept of Test Oracles—pairs of equivalent queries that should yield the same result. The efficiency of these approaches is often limited by human expertise, resulting in low bug coverage.

Recent work has explored using Large Language Models (LLMs) to generate such test oracles, but this approach faces challenges:

- **C1: Slow and Expensive** — LLMs are computationally demanding.
- **C2: Hallucination** — LLMs can generate non-equivalent queries, leading to false alarms.
- **C3: Rigid Generation** — LLMs can produce a limited diversity of test cases, which is crucial for achieving high code coverage.

This project proposes a new pipeline to address these challenges by focusing on the automated discovery of diverse SQL.

We extend this idea by introducing a formal verification layer. We leverage LLMs to scale the generation of diverse SQLs and their SQL instantiations, and use Lean 4 to perform rigorous semantic verification. Each query is translated into a formal representation under bag semantics, and Lean is used to prove equivalence across instantiations and ensure consistency of test oracles.

This combination enables scalable generation with LLMs and proof-level correctness with Lean, turning test oracle construction into a deterministically verifiable process rather than a heuristic one.

## Proposed Methodology

Our methodology integrates LLMs, a diversity metric, and formal verification into an evolutionary loop.

### 1. The Core Pipeline

The project's pipeline is structured as follows:

| Component | Function |
|-----------|----------|
| LLM w/ In-context Learning | Generates new SQL pairs based on existing high-scoring examples. |
| SQL Pool | Stores the generated SQL pairs. |
| Diversity-based Sampling | Selects high-scoring, diverse examples from the SQL Pool to be used as in-context learning prompts for the LLM. |
| Lean-based Verifier | Formally verifies the equivalence of SQL pairs under bag semantics, ensuring proof-level correctness of test oracles. |

### 2. Lean Verifier

The Lean-based Verifier ensures that our generated test queries are formally proven to be equivalent before they are used to find bugs.

This process prevents hallucinations (non-equivalent queries), guaranteeing that any bug found is a real error in the database.

**Example:** Proving two SQL queries are the same.

| SQL Query 1 | SQL Query 2 |
|-------------|-------------|
| `SELECT * FROM R WHERE x > 0 AND x < 10;` | `SELECT * FROM R WHERE x < 10 AND x > 0;` |

The LLM will also generate the potential Lean proof:

```lean
-- A bag relation: each possible row maps to its multiplicity.
abbrev Bag (α : Type) := α → Nat

-- Filter under bag semantics:
-- keep the same multiplicity if p holds, else 0.
def filter (p : α → Prop) [DecidablePred p] (R : Bag α) : Bag α :=
  fun a => if p a then R a else 0

-- Our "table" R has one integer column x, so rows are just Int.
abbrev Row := Int

def q1 (R : Bag Row) : Bag Row :=
  filter (fun x => x > 0 ∧ x < 10) R

def q2 (R : Bag Row) : Bag Row :=
  filter (fun x => x < 10 ∧ x > 0) R

theorem q1_eq_q2 (R : Bag Row) : q1 R = q2 R := by
  funext x
  simp [q1, q2, filter, and_left_comm]

-- If you want the statement "for all tables R, q1 and q2 are equivalent":
theorem sql_equiv : ∀ R : Bag Row, q1 R = q2 R :=
  q1_eq_q2
```

**Proof:**
In database terms (bag semantics), these queries must produce the same result because the AND condition is commutative. The order doesn't change which rows are kept.

The Lean 4 Proof Assistant confirms this: it formalizes the queries as mathematical functions and uses the built-in property that `A AND B` is equivalent to `B AND A` to prove the two functions (queries) are identical.

## Experiments and Expected Results

The experiments will be conducted using the following configuration, based on preliminary results:

| Setting | Value |
|---------|-------|
| Model | O4-mini |
| Iteration Rounds | 1000 |
| Successful Generation Rate | ~30% (Approx. 300 successful oracles) |

We expect the proposed techniques to significantly improve the quantity and diversity of test oracles.

## Lean Evaluation and Project Goal

The primary goal of this project is to create a robust, automated pipeline for discovering diverse, high-quality test oracles to find more logic bugs in mature Database Management Systems (DBMS).

The Lean 4-based formal verification component plays a critical role in achieving this:

- **Verifying SQLs:** By formally translating and proving the equivalence of generated SQL pairs under bag semantics, Lean ensures that the query templates are sound. This process weeds out potentially non-equivalent queries before they are instantiated.
- **Increasing Precision (Eliminating Hallucinations):** The rigorous mathematical proof system of Lean guarantees the semantic equivalence of the test oracles. This verification step directly addresses challenge **C2 (Hallucination)** by ensuring that any failed test in the DBMS is a real bug and not a false alarm caused by a flawed test oracle.

This integration of scalable LLM generation with proof-level correctness via Lean allows the system to focus its evolutionary search on highly diverse, guaranteed-correct test cases, maximizing the chances of uncovering deep, previously missed logic bugs in the target DBMS.

## Future Directions

- Extending the approach to Query Optimization Rules (e.g., finding faster equivalent queries).
- Applying the verification framework to other types of test case generation.

## Project Timeline

We will adhere to the following projected timeline for the project:

| Phase | Description | Key Deliverables |
|-------|-------------|------------------|
| Phase 1: Setup | Environment configuration, integrating LLM, Prover. | SQL Pool structure. |
| Phase 2: Diversity Metric | Implement ZSS Tree-Edit-Distance for Query Plan Similarity (QPS). | Functional QPS Evaluator. |
| Phase 3: Evolution Techniques | Implement and integrate Multi-example Evolution and Far-island Search. | Updated evolution pipeline. |
| Phase 4: Experimentation & Analysis | Execute 1000 iteration runs, collect data on diversity and success rate. | Raw experiment results. |
| Phase 5: Lean Verification | Implement Lean-based equivalence proofs for SQL pairs under bag semantics and integrate with the prover pipeline. | Verified SQL pairs with formal proof certificates. |
| Phase 6: Final Report & Presentation | Analyze results, write the final paper, and prepare the presentation. | Final report and presentation materials. |
