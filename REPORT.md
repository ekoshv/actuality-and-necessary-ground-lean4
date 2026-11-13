# Formalization report

**Article:** *From Mathematical Possibility to Actuality: A Modal-Existential Argument for a Necessary Ground of Concrete Reality*, “A Philosophical Reconstruction,” 20 September 2026. The original 16-page PDF was found on the user's Desktop, read completely by page-labelled text extraction, and its two principal propositions were also inspected as rendered pages. An unchanged copy is included in `source/`; its SHA-256 is `5e13210df5408b365746785757aa8494b53e96e4887115f16470f7445f06a0ea`. The current edition, revised on 28 October 2026 and again on 13 November 2026, is `actuality_and_necessary_ground.pdf` in the repository root; its LaTeX source is `paper/actuality_and_necessary_ground.tex`. It presents the strengthened argument in its Section 5, the derived premises in its Section 6, and this formalization in its Section 17. Throughout this report, "the article" means the first edition.

**Verified on 13 November 2026:** direct Lean type-check, Lake build, and the separate dependency audit all exited **0**. All **69 theorems** passed. The audit reports 70, because it also covers `GroundingLevel.brecOn`, the recursion lemma that Lean generates for that inductive definition. Of the 69, fifty-two have no axiom dependencies; seventeen use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. There are no added axioms or admitted proofs. The exact Lean 4.19.0 compiler, mathlib revision, and source hashes are recorded in `compilation_output.txt`. The first 25 theorems formalize the article; the next 15 form the strengthened argument; the last 29 derive its two added premises and treat the grounding fact. Both additions are described below. The 25 article theorems were first verified on 18 October 2026, and the first 40 on 28 October 2026.

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

## Derived premises (second revision)

This section also goes beyond the article; the current edition presents it in its Section 6. Three criticisms of the strengthened argument motivate it.

- P10\* and P3\* stand close to the conclusion. Together they say that a complete ground of the totality has a concrete member and no contingent member.
- The modal core does not separate mathematics from the necessary concrete ground. By `ground_does_not_necessitate`, neither can necessitate a contingent totality, so only P3\* excluded mathematics.
- `grounds` had no structure, and the fact that a ground grounds the totality was not itself a proposition. `Models.fullGround_not_irreflexive` shows that in the joint model of the strengthened premises one collection grounds every actual truth, including the obtaining of its own members.

Four finer premises replace P10\* and P3\*. All are theorem arguments.

- **Irreflexivity** (`GroundIrreflexive`): no collection grounds the obtaining of one of its own members.
- **Dissectivity** (`Dissective`): a complete ground of the totality also grounds the obtaining of each contingent member of that ground. This is the article's rationale for P10. For the `TotalFact` construction it follows from `GroundsConjuncts` and factivity.
- **Production principle** (`NonNecessitatingGroundsProduce`): a complete ground that does not necessitate what it grounds has a member satisfying the interpreted predicate `productive`.
- **Inertness**: abstract candidates are not productive. In the theorems it appears as "mathematical candidates are not productive" or as "whatever is productive is concrete."

| Result | Formal theorem | Exact result |
|---|---|---|
| P10\* derived | `ultimacy_of_irreflexive_dissective` | Irreflexivity and dissectivity imply P10\*. |
| P10\* for the conjunction | `total_fact_dissective`, `total_fact_ultimacy` | For `TotalFact`, irreflexivity, grounding of conjuncts, and factivity imply P10\*. |
| Modal core for collections | `necessary_collection_does_not_necessitate` | A collection of necessarily obtaining candidates does not necessitate a contingent fact. |
| Mathematics alone | `inert_necessities_cannot_ground`, `mathematics_alone_cannot_ground` | If mathematical candidates are necessary and unproductive, C is contingent, and the production principle holds, no collection of mathematical candidates grounds C. Neither PSR, P10\*, nor P3\* is used. |
| P3\* derived | `productive_member_of_ultimate_ground`, `abstract_insufficiency_of_production` | Under contingency, P10\*, factivity, self-access, and the production principle, every complete ground of C has a productive member. With inertness, P3\* follows. |
| Productive ground | `necessary_productive_ground` | Some complete ground of C has a productive, concrete member that actually and necessarily obtains. |
| Combined | `derived_argument` | From contingency, PSR, irreflexivity, dissectivity, factivity, self-access, the production principle, and inertness: modal non-selection, a productive concrete necessary member, and non-necessitation. P10\* and P3\* are not premises. |

A second group of theorems indexes grounding to evaluations: `groundsAt v G p` says that G grounds p at v, and `FactiveAt` is factivity at every accessible evaluation.

| Result | Formal theorem | Exact result |
|---|---|---|
| Van Inwagen's lemma | `necessitating_fact_is_contingent` | Given self-access, an actually obtaining proposition that necessitates a contingent C is contingent. |
| The link necessitates | `grounding_fact_necessitates` | By factivity, the grounding fact necessitates what is grounded. |
| The link is contingent | `grounding_fact_contingent` | If C is contingent and G actually grounds C, the fact that G grounds C is contingent. P10\* is not used. |
| Ground without grounding | `ground_obtains_without_grounding` | Under P10\*, at some accessible evaluation every member of G obtains and G does not ground C. |
| Regress | `grounding_level_contingent`, `grounding_regress` | If PSR's domain is closed under grounding facts, `GroundingLevel` has an actual, contingent, PSR-eligible fact at every level. |
| No contrastive explanation | `no_level_settles_the_contrast` | If P10\* holds at every level, each ground obtains at some accessible evaluation where the fact it grounds fails. |

Propositions are functions from evaluations to `Prop`, so they are individuated by where they hold. The levels of `GroundingLevel` therefore need not be distinct facts, and the regress may be a fixed point in which one ground serves at every level.

The models for this part:

- `Models.derived_premises_satisfiable`: every premise of `derived_argument` holds with a contingent world. Grounding is `strictGroundAt`, under which only contingent truths are grounded, by a mathematical candidate together with a necessary concrete one.
- `Models.indexed_premises_satisfiable`: the premises of `grounding_regress` and `no_level_settles_the_contrast` hold in the same model, so the regress is consistent.
- `Models.dropping_irreflexivity_countermodel`: a contingent candidate grounds its own obtaining; dissectivity holds and P10\* fails.
- `Models.dropping_dissectivity_countermodel`: in a four-world model, two independent contingent candidates ground their joint obtaining; ground is irreflexive and P10\* fails.
- `Models.dropping_production_countermodel` and `Models.dropping_inertness_countermodel`: without either premise, a mathematical candidate alone grounds the world.
- `Models.dropping_self_access_countermodel`: in a three-world model whose actual evaluation does not access itself, every other premise of `necessary_concrete_ground` holds and nothing is necessary.
- `Models.dropping_factivity_strong_countermodel`: an impossible concrete candidate satisfies PSR, P10\*, and P3\*.

What the second revision does not do. The four finer premises are still premises. The production principle in particular is contested: it presupposes that some full grounds do not necessitate, against the orthodox view of ground. And the regress theorems state a limit of the argument. Whatever settles why C obtains rather than fails is contingent, so by P10\* it lies outside the ultimate ground and inside what was to be explained. The argument therefore offers an explanation of the fact that contingent actuality obtains, and no explanation of why this actuality obtains rather than another. A motivation for PSR that appeals to what could have been otherwise is contrastive, and the argument does not satisfy it.

## Models and verification

The source includes proved two-world models and countermodels:

- Possibility can hold without actuality at the designated evaluation.
- Removing contingency permits mathematical necessitation.
- Removing PSR permits brute contingent actuality with no ground.
- Removing P10 permits PSR and factivity with only contingent grounds.
- Removing factivity permits a non-contingent but impossible ground candidate.
- All premises of the designated-C theorem have an explicit joint model with contingent effects. A further model satisfies the premises for the explicit `TotalFact` construction, with both necessary and contingent entities. Thus these formal packages are satisfiable relative to Lean's foundations; they do not smuggle in necessitation of the effect.
- A necessary component can coexist with contingent obtaining of the whole collection. An arbitrary additional theological attribute can consistently be interpreted as false.
- The strengthened argument and the derived premises have their own joint models and countermodels, listed in the two previous sections. Two of those use three and four worlds.

`compilation_output.txt` records the compiler identity, pinned dependency revision, source hashes, direct source type-check, Lake build, and transitive dependency audit. `Audit.lean` inspects every theorem in the `ActualityGround` namespace and rejects any project axiom or any transitive axiom outside Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. These foundational principles are distinguished from the unproved philosophical premises above. No admitted proof, arbitrary philosophical axiom declaration, or native-computation proof shortcut is used.

See `README.md` for the pinned environment and reproduction commands. The formal result verifies the conditional reasoning; it leaves the truth of its metaphysical premises open, as the article itself does.
