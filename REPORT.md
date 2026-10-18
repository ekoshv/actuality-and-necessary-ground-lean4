# Formalization report

**Article:** *From Mathematical Possibility to Actuality: A Modal-Existential Argument for a Necessary Ground of Concrete Reality*, “A Philosophical Reconstruction,” 20 September 2026. The original 16-page PDF was found on the user's Desktop, read completely by page-labelled text extraction, and its two principal propositions were also inspected as rendered pages. An unchanged copy is included in `source/`; its SHA-256 is `5e13210df5408b365746785757aa8494b53e96e4887115f16470f7445f06a0ea`.

**Verified on 18 October 2026:** direct Lean type-check, Lake build, and the separate dependency audit all exited **0**. All **25 theorems** passed. Nineteen have no axiom dependencies; six use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms or admitted proofs. The exact Lean 4.19.0 compiler, mathlib revision, and source hashes are recorded in `compilation_output.txt`.

## What is proved

The formal targets are Proposition 1 on page 5, Proposition 2 on page 6, the twelve-step reconstruction on page 12, and the modal-collapse objection on page 10. `ActualityGround.lean` gives proofs of the following conditional results.

| Source claim | Formal theorem | Exact result |
|---|---|---|
| P5: modal distribution | `box_modus_ponens` | Necessarily N and necessarily (N implies C) entail necessarily C. |
| Proposition 1 / P6 | `modal_non_selection` | Necessarily N and contingent C entail that (N implies C) is not necessary. |
| Proposition 2 / P9–P11 | `noncontingent_ground_consequence` | Actual contingent C, PSR applicable to C, and P10 entail a complete ground containing a non-contingent member. |
| Explicit necessity bridge | `necessary_of_actual_noncontingent` | An actually obtaining, non-contingent proposition is necessary, provided the actual evaluation is accessible from itself. |
| Carefully scoped P12 | `necessary_ground_consequence` | With grounding factivity added, some complete ground of C contains an actually and necessarily obtaining member. |
| Combined reconstruction | `refined_argument` | The non-selection result and the necessary-component result hold together under their listed premises. |
| Optional realization of P8 | `total_fact_actual`, `total_fact_contingent`, `represented_totality_necessary_ground` | A conjunction of all represented actual contingent facts obtains actually; a represented contingent member makes that conjunction contingent. The ground result then follows if PSR covers this total and P10 holds for it. |
| Modal-collapse concern | `necessary_ground_cannot_necessitate_contingent_effect` | A necessarily obtaining ground cannot necessitate a contingent effect through a necessary implication. |

The modal core follows directly from the semantics on an arbitrary accessibility relation. No S5 assumption or philosophical axiom is needed for the logical implication itself. Necessity of the relevant mathematical facts is still a premise when the theorem is applied to mathematics.

## Premises that remain unproved

Every philosophical premise is a theorem argument or an interpreted predicate, never a new Lean axiom declaration.

- **P1–P3, interpretation:** `N` represents the relevant mathematical facts and `C` represents concrete actuality. Their representational adequacy, and the abstract/concrete distinction, are not established by defining different predicates. Mathematical existence is not equated with Lean type inhabitation.
- **P2:** `Box R N w` says the relevant mathematical facts are necessary. The formalization does not derive metaphysical necessity from mathematical truth.
- **P4/P8:** the designated total actuality actually obtains and is contingent. For the optional `TotalFact` construction, actuality and contingency are derived from its definition and an actual contingent member; whether the represented domain exhausts reality remains an interpretation assumption.
- **P7 / PSR-A:** `RestrictedPSR` requires complete grounds for actual contingent concrete facts. The separate `concrete C` premise explicitly admits the totality to PSR's domain. Explanation of each member does not establish this admission.
- **P10:** `NoWhollyContingentGround` prohibits any wholly contingent collection from completely grounding C. This is a strong substantive premise, not something deduced from the word “ground,” irreflexivity, or the existence of individual explanations. Once a complete ground is given, this premise does most of the work in extracting a non-contingent component.
- **Factivity:** `GroundFactivity` says a complete actual ground's members actually obtain. This makes explicit the article's implicit existence commitment. Without it, “non-contingent” includes the impossible and does not imply necessary existence.

## Scope and modeling choices

Propositions are functions from modal evaluations to `Prop`. Grounding realities/facts have a separate rigid domain, with `holds g w` expressing their existence or obtaining. A ground is an arbitrary mathlib `Set` of candidates, allowing infinite collections. “Wholly contingent” means that every member is contingent. The article's last step is therefore formalized as **a necessary component of a complete ground**; it does not establish that the whole collection, every member, or its explanatory relation is necessary. The alternative reading in which “wholly contingent” means contingency of the collection as one object would require a different model.

For the necessity bridge, `R w w` explicitly supplies accessibility of the actual evaluation from itself. Necessity is relative to the worlds accessible from that evaluation; no conclusion about inaccessible worlds is claimed. The existence and exhaustiveness of metaphysically possible worlds remain part of the interpretation of the model.

`grounds` is an uninterpreted complete-explanation relation. Factivity connects it to actual obtaining; it is not defined as necessary implication. No temporal ordering or prohibition of every infinite regress is assumed. This permits timeless grounding but does not prove a physical block-universe theory.

The necessary component is not proved unique, personal, good, omniscient, nonmathematical, or identifiable with God. Gödel's incompleteness theorems, quantum physics, and the historical interpretations in sections 5–11 are contextual discussion and are not proved in this development.

## Models and verification

The source includes proved two-world models and countermodels:

- Possibility can hold without actuality at the designated evaluation.
- Removing contingency permits mathematical necessitation.
- Removing PSR permits brute contingent actuality with no ground.
- Removing P10 permits PSR and factivity with only contingent grounds.
- Removing factivity permits a non-contingent but impossible ground candidate.
- All premises of the designated-C theorem have an explicit joint model with contingent effects. A further model satisfies the premises for the explicit `TotalFact` construction, with both necessary and contingent entities. Thus these formal packages are satisfiable relative to Lean's foundations; they do not smuggle in necessitation of the effect.
- A necessary component can coexist with contingent obtaining of the whole collection. An arbitrary additional theological attribute can consistently be interpreted as false.

`compilation_output.txt` records the compiler identity, pinned dependency revision, source hashes, direct source type-check, Lake build, and transitive dependency audit. `Audit.lean` inspects every theorem in the `ActualityGround` namespace and rejects any project axiom or any transitive axiom outside Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. These foundational principles are distinguished from the unproved philosophical premises above. No admitted proof, arbitrary philosophical axiom declaration, or native-computation proof shortcut is used.

See `README.md` for the pinned environment and reproduction commands. The formal result verifies the conditional reasoning; it leaves the truth of its metaphysical premises open, as the article itself does.
