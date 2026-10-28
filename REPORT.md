# Formalization report

**Article:** *From Mathematical Possibility to Actuality: A Modal-Existential Argument for a Necessary Ground of Concrete Reality*, “A Philosophical Reconstruction,” 20 September 2026. The original 16-page PDF was found on the user's Desktop, read completely by page-labelled text extraction, and its two principal propositions were also inspected as rendered pages. An unchanged copy is included in `source/`; its SHA-256 is `5e13210df5408b365746785757aa8494b53e96e4887115f16470f7445f06a0ea`. A revised edition of 28 October 2026, which presents the strengthened argument in its Section 5 and reports this formalization in its Section 15, is `actuality_and_necessary_ground.pdf` in the repository root; its LaTeX source is `paper/actuality_and_necessary_ground.tex`. Throughout this report, "the article" means the first edition.

**Verified on 28 October 2026:** direct Lean type-check, Lake build, and the separate dependency audit all exited **0**. All **40 theorems** passed. Twenty-nine have no axiom dependencies; eleven use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms or admitted proofs. The exact Lean 4.19.0 compiler, mathlib revision, and source hashes are recorded in `compilation_output.txt`. The first 25 theorems formalize the article; the other 15 form the strengthened argument described below. The 25 article theorems were first verified on 18 October 2026.

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

Under the article's premises, the necessary component is not proved unique, personal, good, omniscient, nonmathematical, or identifiable with God. The strengthened argument below adds P3\*, under which it is concrete; the other attributes remain unproved. Gödel's incompleteness theorems, quantum physics, and the historical interpretations in sections 5–11 are contextual discussion and are not proved in this development.

## Strengthened argument (revised edition)

This section goes beyond the article; the revised edition presents it in its Section 5. P10 excludes only grounds all of whose members are contingent. `Models.original_P10_met_by_mathematics` shows the consequence. Contingent concrete reality padded with a mathematical candidate satisfies PSR, P10, and factivity. The formal conclusion is then met with the mathematical candidate as the necessarily obtaining member, and no complete ground has a necessary concrete member. The article's rationale for P10 applies to each contingent member, not only to wholly contingent collections. Its claim that the ground lies "beyond merely possible mathematical description" needs a premise the article never states.

Two premises close these gaps. Both are theorem arguments, not axioms.

- **P10\*, ultimacy** (`NoContingentMember`): no member of a complete ground of the designated totality is contingent. It constrains only complete grounds of that totality, not explanations of facts within it.
- **P3\*, abstract insufficiency** (`AbstractInsufficiency`): every complete ground of the totality has a member satisfying the interpreted predicate `concreteE`. Abstract candidates alone, including mathematical ones, cannot ground it. The concreteness classification is an interpretation assumption, as `concrete` is for the PSR domain.

| Result | Formal theorem | Exact result |
|---|---|---|
| Strengthening | `strengthened_premises_imply_P10` | P10\* and P3\* imply P10, so every earlier theorem applies under them. |
| P12\* | `necessary_concrete_ground` | With PSR, P10\*, P3\*, factivity, and self-access, some complete ground of C has a concrete member that actually and necessarily obtains. |
| Non-contrastive ground | `ground_obtains_where_C_fails` | If C is contingent, then under P10\*, factivity, and self-access, every member of every complete ground of C obtains at some accessible evaluation where C fails. |
| Non-necessitation | `ground_does_not_necessitate` | Under the same premises, no complete ground of C necessitates C. |
| Dilemma | `brute_fact_or_noncontingent_concretum` | Under P10\* and P3\*, either C has no complete ground, or some concrete candidate is non-contingent. |
| Abstract necessity alone | `abstract_necessity_alone_cannot_ground` | Under P10\* and P3\*, if every non-contingent candidate is abstract, C has no complete ground. |
| Combined | `strengthened_argument` | Modal non-selection, P12\*, and non-necessitation hold together. |

`Models.strengthened_premises_satisfiable` is a joint two-world model of P2, P4, PSR, P10\*, P3\*, and factivity with a contingent world. The strengthened premises therefore do not collapse modality; the ground in that model is a mathematical candidate together with a necessary concrete one. Each new premise is essential:

- `Models.dropping_AI_countermodel`: without P3\*, a mathematical candidate alone grounds the world.
- `Models.dropping_strong_nc_countermodel`: without P10\*, contingent concrete reality grounds the world and no complete ground has a necessary member.
- `Models.dropping_PSR_strong_countermodel`: without PSR, the world is a brute contingent fact while P10\*, P3\*, and factivity hold vacuously.

`Models.strengthened_ground_need_not_be_personal` adds that nothing in the strengthened argument makes the necessary concrete member personal. Under one reading of an arbitrary further attribute, every strengthened premise and the conclusion hold while no member of any complete ground has the attribute.

The cost is made explicit rather than removed. Van Inwagen's modal-collapse argument assumes that an explanation necessitates what it explains. `ground_does_not_necessitate` shows that, given contingency and P10\*, no complete ground of the totality can. Whoever requires necessitating explanation must therefore reject PSR for the totality, or contingency. Whoever keeps both must accept an ultimate explanation that is non-necessitating and, by `ground_obtains_where_C_fails`, non-contrastive, as with free choice or objective chance.

The conclusion is neutral between theistic and naturalistic readings. A necessarily existing initial physical state with chancy evolution satisfies it. Uniqueness, personhood, goodness, and identification with God remain unproved.

## Models and verification

The source includes proved two-world models and countermodels:

- Possibility can hold without actuality at the designated evaluation.
- Removing contingency permits mathematical necessitation.
- Removing PSR permits brute contingent actuality with no ground.
- Removing P10 permits PSR and factivity with only contingent grounds.
- Removing factivity permits a non-contingent but impossible ground candidate.
- All premises of the designated-C theorem have an explicit joint model with contingent effects. A further model satisfies the premises for the explicit `TotalFact` construction, with both necessary and contingent entities. Thus these formal packages are satisfiable relative to Lean's foundations; they do not smuggle in necessitation of the effect.
- A necessary component can coexist with contingent obtaining of the whole collection. An arbitrary additional theological attribute can consistently be interpreted as false.
- The strengthened argument has its own joint model and countermodels, listed in the previous section.

`compilation_output.txt` records the compiler identity, pinned dependency revision, source hashes, direct source type-check, Lake build, and transitive dependency audit. `Audit.lean` inspects every theorem in the `ActualityGround` namespace and rejects any project axiom or any transitive axiom outside Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. These foundational principles are distinguished from the unproved philosophical premises above. No admitted proof, arbitrary philosophical axiom declaration, or native-computation proof shortcut is used.

See `README.md` for the pinned environment and reproduction commands. The formal result verifies the conditional reasoning; it leaves the truth of its metaphysical premises open, as the article itself does.
