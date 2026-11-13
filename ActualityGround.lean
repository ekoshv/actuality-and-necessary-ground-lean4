import Mathlib.Data.Set.Basic

/-!
# From Mathematical Possibility to Actuality: a conditional formalization

Source: `actuality_and_necessary_ground.pdf`, 20 September 2026, 16 pages.
The formal targets are Proposition 1 (p. 5), Proposition 2 (p. 6),
the twelve steps (p. 12), and the modal-collapse objection (p. 10).
A further section strengthens the argument with two premises that are not in
the source, P10* and P3*, and proves what they add and what they cost.
The last part derives P10* and P3* from finer premises (irreflexivity,
dissectivity, a production principle, inertness of abstract entities) and
indexes grounding to evaluations, so that the grounding fact is itself a
proposition.

All philosophical principles are explicit arguments of the theorems below.
In particular, PSR and the exclusion of wholly contingent complete grounds
are not asserted as facts of logic. Grounding is an uninterpreted relation.

`World` is a space of modal evaluations, not the particular concrete universe
whose actuality is represented by a proposition `C : World -> Prop`.
`Entity` is a rigid domain of candidate grounding realities/facts; `holds g w`
expresses their existence/obtaining, rather than making Lean's type inhabitation
stand for concrete existence. Collections use mathlib's `Set` and may be infinite.

Necessity is relative to accessibility from the designated evaluation. No
seriality, transitivity, symmetry or S5 assumption is needed for Proposition 1.
The existence-to-necessity bridge needs only accessibility of the actual world
from itself. The constructed examples use universal accessibility (an S5 frame).
-/

namespace ActualityGround

universe u v

abbrev WProp (World : Type u) := World → Prop

def Box {World : Type u} (R : World → World → Prop)
    (p : WProp World) (w : World) : Prop :=
  ∀ v, R w v → p v

def Diamond {World : Type u} (R : World → World → Prop)
    (p : WProp World) (w : World) : Prop :=
  ∃ v, R w v ∧ p v

def Contingent {World : Type u} (R : World → World → Prop)
    (p : WProp World) (w : World) : Prop :=
  Diamond R p w ∧ Diamond R (fun v => ¬ p v) w

section Modal

variable {World : Type u} {R : World → World → Prop}
variable {N p : WProp World} {w : World}

/-- P5, and the semantic proof of normal modal distribution/K. -/
theorem box_modus_ponens (hN : Box R N w)
    (himp : Box R (fun v => N v → p v) w) : Box R p w := by
  intro v hv
  exact himp v hv (hN v hv)

theorem contingent_not_necessary (hc : Contingent R p w) : ¬ Box R p w := by
  intro hp
  obtain ⟨v, hv, hnp⟩ := hc.2
  exact hnp (hp v hv)

/-- Proposition 1 / P6. Mathematical necessity and contingency are premises. -/
theorem modal_non_selection (hN : Box R N w) (hc : Contingent R p w) :
    ¬ Box R (fun v => N v → p v) w := by
  intro himp
  exact contingent_not_necessary hc (box_modus_ponens hN himp)

/-- The modal-collapse objection has exactly the same logical form. -/
theorem necessary_ground_cannot_necessitate_contingent_effect
    (hG : Box R N w) (hc : Contingent R p w) :
    ¬ Box R (fun v => N v → p v) w :=
  modal_non_selection hG hc

/-- Non-contingency alone also allows impossibility. Actual obtaining excludes it.
    `hrefl` is an explicit semantic assumption, and classical logic is used. -/
theorem necessary_of_actual_noncontingent (hrefl : R w w)
    (hp : p w) (hnc : ¬ Contingent R p w) : Box R p w := by
  classical
  intro v hv
  by_contra hnp
  exact hnc ⟨⟨w, hrefl, hp⟩, ⟨v, hv, hnp⟩⟩

end Modal

section Grounding

variable {World : Type u} {Entity : Type v}

/-- This is the article's componentwise reading of "wholly contingent".
    The collection is evaluated de re: the same candidate entities occur at
    every world. This is a modeling choice, not a theorem about metaphysics. -/
def WhollyContingent (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World) (G : Set Entity) : Prop :=
  ∀ g ∈ G, Contingent R (holds g) w

/-- P7/PSR-A, restricted to designated concrete facts that actually obtain.
    The conclusion is a complete explanation, not modal necessitation. -/
def RestrictedPSR (R : World → World → Prop) (w : World)
    (concrete : WProp World → Prop)
    (grounds : Set Entity → WProp World → Prop) : Prop :=
  ∀ p, concrete p → p w → Contingent R p w → ∃ G, grounds G p

/-- P10 / Proposition 2(iii). This strong philosophical premise is NOT derived
    from irreflexivity, the explanation of individual members, or modal logic. -/
def NoWhollyContingentGround (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World)
    (grounds : Set Entity → WProp World → Prop) (C : WProp World) : Prop :=
  ∀ G, WhollyContingent R holds w G → ¬ grounds G C

/-- Explicit bridge: a complete actual ground and all its members obtain.
    This is a substantive interpretation of actual complete grounding.
    It does NOT say that grounding necessitates its effect at other worlds. -/
def GroundFactivity (w : World) (holds : Entity → WProp World)
    (grounds : Set Entity → WProp World → Prop) : Prop :=
  ∀ G p, grounds G p → p w ∧ ∀ g ∈ G, holds g w

variable {R : World → World → Prop} {holds : Entity → WProp World}
variable {w : World} {grounds : Set Entity → WProp World → Prop}
variable {concrete : WProp World → Prop} {C : WProp World}

/-- P11: a complete ground exists and includes a non-contingent member.
    No factivity or modal frame assumption is needed for this weaker result. -/
theorem noncontingent_component_of_complete_ground
    (hex : ∃ G, grounds G C)
    (h10 : NoWhollyContingentGround R holds w grounds C) :
    ∃ G, grounds G C ∧ ∃ g ∈ G, ¬ Contingent R (holds g) w := by
  classical
  obtain ⟨G, hG⟩ := hex
  refine ⟨G, hG, ?_⟩
  by_contra hnone
  apply h10 G ?_ hG
  intro g hg
  by_contra hnc
  exact hnone ⟨g, hg, hnc⟩

/-- Proposition 2, through the non-contingent conclusion. `C` is a designated
    total actuality; its interpretation as a totality is an application premise. -/
theorem noncontingent_ground_consequence
    (hCactual : C w) (hCcont : Contingent R C w) (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (h10 : NoWhollyContingentGround R holds w grounds C) :
    ∃ G, grounds G C ∧ ∃ g ∈ G, ¬ Contingent R (holds g) w :=
  noncontingent_component_of_complete_ground
    (hPSR C hCconcrete hCactual hCcont) h10

/-- P12, carefully scoped: at least one actual complete ground contains a
    necessarily obtaining member. Neither uniqueness nor necessity of every
    member, nor any theological attribute, is included in the conclusion. -/
theorem necessary_ground_consequence
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (h10 : NoWhollyContingentGround R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds) :
    ∃ G, grounds G C ∧ ∃ g ∈ G, holds g w ∧ Box R (holds g) w := by
  obtain ⟨G, hG, g, hg, hnc⟩ :=
    noncontingent_ground_consequence hCactual hCcont hCconcrete hPSR h10
  have hactual := (hfactive G C hG).2 g hg
  exact ⟨G, hG, g, hg, hactual,
    necessary_of_actual_noncontingent hrefl hactual hnc⟩

/-- The two arguments are independent conditional results. In particular, P6
    alone is not used to infer PSR, P10, or existence of any ground. -/
theorem refined_argument
    {N : WProp World} (hN : Box R N w)
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (h10 : NoWhollyContingentGround R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds) :
    (¬ Box R (fun v => N v → C v) w) ∧
    (∃ G, grounds G C ∧ ∃ g ∈ G, holds g w ∧ Box R (holds g) w) :=
  ⟨modal_non_selection hN hCcont,
    necessary_ground_consequence hrefl hCactual hCcont hCconcrete hPSR h10 hfactive⟩

/-- Optional precise realization of P8: the conjunction of all represented
    actual contingent facts. The PDF explicitly permits other totality models.
    This quantification is over Entity, not an impredicative "set of all facts". -/
def TotalFact (R : World → World → Prop) (holds : Entity → WProp World)
    (w : World) : WProp World :=
  fun v => ∀ e, (holds e w ∧ Contingent R (holds e) w) → holds e v

theorem total_fact_actual : TotalFact R holds w w := by
  intro e he
  exact he.1

/-- In this chosen conjunction model, a represented actual contingent member
    suffices for contingency of the total fact; PSR for that total is separate. -/
theorem total_fact_contingent (hrefl : R w w)
    (hex : ∃ e, holds e w ∧ Contingent R (holds e) w) :
    Contingent R (TotalFact R holds w) w := by
  obtain ⟨e, he⟩ := hex
  obtain ⟨v, hv, hne⟩ := he.2.2
  refine ⟨⟨w, hrefl, total_fact_actual⟩, v, hv, ?_⟩
  intro htotal
  exact hne (htotal e he)

/-- Full ground consequence for the optional represented-totality construction.
    The total's actuality and contingency are derived, but its admission into
    the PSR domain and P10 for that total remain explicit premises. -/
theorem represented_totality_necessary_ground
    (hrefl : R w w)
    (hex : ∃ e, holds e w ∧ Contingent R (holds e) w)
    (hCconcrete : concrete (TotalFact R holds w))
    (hPSR : RestrictedPSR R w concrete grounds)
    (h10 : NoWhollyContingentGround R holds w grounds (TotalFact R holds w))
    (hfactive : GroundFactivity w holds grounds) :
    ∃ G, grounds G (TotalFact R holds w) ∧
      ∃ g ∈ G, holds g w ∧ Box R (holds g) w :=
  necessary_ground_consequence hrefl total_fact_actual
    (total_fact_contingent hrefl hex) hCconcrete hPSR h10 hfactive

end Grounding

/-! ## Strengthened argument

The original P10 excludes only grounds whose members are all contingent, so a
contingent ground padded with a necessary mathematical truth satisfies it
(`Models.original_P10_met_by_mathematics`). Two premises that are not in the
source close that gap. P10* applies P10's own rationale to every member of a
complete ground of the totality, and P3* says that abstract entities alone
cannot completely ground concrete actuality. Under them the conclusion
concerns a necessarily existing concrete member, and the modal-collapse worry
becomes a theorem about how that member grounds: never by necessitation.
-/

section Strengthened

variable {World : Type u} {Entity : Type v}

/-- P10*, ultimacy: no member of a complete ground of `C` is contingent.
    P10's rationale, that a contingent ground's own actuality remains within
    what was to be explained, is applied to each member. It constrains only
    complete grounds of the designated totality, not explanations of single
    facts within it. -/
def NoContingentMember (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World)
    (grounds : Set Entity → WProp World → Prop) (C : WProp World) : Prop :=
  ∀ G, grounds G C → ∀ g ∈ G, ¬ Contingent R (holds g) w

/-- P3*, abstract insufficiency: every complete ground of `C` has a concrete
    member, so abstract entities such as mathematical structures cannot
    ground `C` on their own. `concreteE` is an interpreted predicate on
    candidate grounds, separate from the PSR domain predicate `concrete`. -/
def AbstractInsufficiency (concreteE : Entity → Prop)
    (grounds : Set Entity → WProp World → Prop) (C : WProp World) : Prop :=
  ∀ G, grounds G C → ∃ g ∈ G, concreteE g

variable {R : World → World → Prop} {holds : Entity → WProp World}
variable {w : World} {grounds : Set Entity → WProp World → Prop}
variable {concrete : WProp World → Prop} {concreteE : Entity → Prop}
variable {C : WProp World}

/-- The strengthened premises imply the original P10, so every earlier
    theorem also holds under them. -/
theorem strengthened_premises_imply_P10
    (hstrong : NoContingentMember R holds w grounds C)
    (hAI : AbstractInsufficiency concreteE grounds C) :
    NoWhollyContingentGround R holds w grounds C := by
  intro G hwhole hG
  obtain ⟨g, hg, _⟩ := hAI G hG
  exact hstrong G hG g hg (hwhole g hg)

/-- P12*: some complete ground of `C` has a concrete member that actually and
    necessarily obtains. An abstract member, such as a mathematical truth,
    cannot be the witness. -/
theorem necessary_concrete_ground
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (hstrong : NoContingentMember R holds w grounds C)
    (hAI : AbstractInsufficiency concreteE grounds C)
    (hfactive : GroundFactivity w holds grounds) :
    ∃ G, grounds G C ∧ ∃ g ∈ G, concreteE g ∧ holds g w ∧ Box R (holds g) w := by
  obtain ⟨G, hG⟩ := hPSR C hCconcrete hCactual hCcont
  obtain ⟨g, hg, hgc⟩ := hAI G hG
  have hactual := (hfactive G C hG).2 g hg
  exact ⟨G, hG, g, hg, hgc, hactual,
    necessary_of_actual_noncontingent hrefl hactual (hstrong G hG g hg)⟩

/-- Every complete ground of a contingent `C` still obtains at some accessible
    evaluation where `C` fails. No complete ground therefore settles why `C`
    obtains rather than its absence: under P10* the ultimate explanation of
    the totality is non-contrastive. -/
theorem ground_obtains_where_C_fails
    (hrefl : R w w) (hCcont : Contingent R C w)
    (hstrong : NoContingentMember R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    {G : Set Entity} (hG : grounds G C) :
    ∃ v, R w v ∧ ¬ C v ∧ ∀ g ∈ G, holds g v := by
  obtain ⟨v, hv, hnC⟩ := hCcont.2
  exact ⟨v, hv, hnC, fun g hg =>
    necessary_of_actual_noncontingent hrefl ((hfactive G C hG).2 g hg)
      (hstrong G hG g hg) v hv⟩

/-- Hence no complete ground of a contingent `C` necessitates it. Van Inwagen's
    modal-collapse dilemma becomes a theorem about the mode of ultimate
    grounding: it is never necessitation. -/
theorem ground_does_not_necessitate
    (hrefl : R w w) (hCcont : Contingent R C w)
    (hstrong : NoContingentMember R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    {G : Set Entity} (hG : grounds G C) :
    ¬ Box R (fun v => (∀ g ∈ G, holds g v) → C v) w := by
  intro hnec
  obtain ⟨v, hv, hnC, hall⟩ :=
    ground_obtains_where_C_fails hrefl hCcont hstrong hfactive hG
  exact hnC (hnec v hv hall)

/-- Under P10* and P3*, either some concrete entity is non-contingent, or the
    totality has no complete ground and is a brute fact. -/
theorem brute_fact_or_noncontingent_concretum
    (hstrong : NoContingentMember R holds w grounds C)
    (hAI : AbstractInsufficiency concreteE grounds C) :
    (¬ ∃ G, grounds G C) ∨ ∃ g, concreteE g ∧ ¬ Contingent R (holds g) w := by
  classical
  by_cases h : ∃ G, grounds G C
  · obtain ⟨G, hG⟩ := h
    obtain ⟨g, hg, hgc⟩ := hAI G hG
    exact Or.inr ⟨g, hgc, hstrong G hG g hg⟩
  · exact Or.inl h

/-- If every non-contingent entity is abstract, as when the only necessary
    things are mathematical, the totality has no complete ground under P10*
    and P3*. Mathematics alone cannot ground concrete actuality. -/
theorem abstract_necessity_alone_cannot_ground
    (hstrong : NoContingentMember R holds w grounds C)
    (hAI : AbstractInsufficiency concreteE grounds C)
    (honly : ∀ g, ¬ Contingent R (holds g) w → ¬ concreteE g) :
    ¬ ∃ G, grounds G C := by
  rintro ⟨G, hG⟩
  obtain ⟨g, hg, hgc⟩ := hAI G hG
  exact honly g (hstrong G hG g hg) hgc

/-- The strengthened argument in one statement: mathematics alone does not
    necessitate `C`, some complete ground of `C` has a necessarily existing
    concrete member, and that ground does not necessitate `C`. -/
theorem strengthened_argument
    {N : WProp World} (hN : Box R N w)
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (hstrong : NoContingentMember R holds w grounds C)
    (hAI : AbstractInsufficiency concreteE grounds C)
    (hfactive : GroundFactivity w holds grounds) :
    (¬ Box R (fun v => N v → C v) w) ∧
    ∃ G, grounds G C ∧
      (∃ g ∈ G, concreteE g ∧ holds g w ∧ Box R (holds g) w) ∧
      ¬ Box R (fun v => (∀ g ∈ G, holds g v) → C v) w := by
  obtain ⟨G, hG⟩ := hPSR C hCconcrete hCactual hCcont
  obtain ⟨g, hg, hgc⟩ := hAI G hG
  have hactual := (hfactive G C hG).2 g hg
  exact ⟨modal_non_selection hN hCcont, G, hG,
    ⟨g, hg, hgc, hactual,
      necessary_of_actual_noncontingent hrefl hactual (hstrong G hG g hg)⟩,
    ground_does_not_necessitate hrefl hCcont hstrong hfactive hG⟩

end Strengthened

/-! ## Explicit finite models and countermodels
These are proved propositions, rather than simulations or trusted computations.
They delimit exactly what the conditional arguments establish.
-/

namespace Models

def allAccess (_ _ : Bool) : Prop := True
def sometimes (w : Bool) : Prop := w = true
def allConcrete (_ : WProp Bool) : Prop := True

theorem sometimes_contingent : Contingent allAccess sometimes true := by
  exact ⟨⟨true, True.intro, rfl⟩, ⟨false, True.intro, by intro h; cases h⟩⟩

theorem sometimes_not_necessary : ¬ Box allAccess sometimes true :=
  contingent_not_necessary sometimes_contingent

theorem always_not_contingent :
    ¬ Contingent allAccess (fun _ : Bool => True) true := by
  intro h
  obtain ⟨v, _, hn⟩ := h.2
  exact hn True.intro

/-- A possible proposition can fail at the designated actual world. -/
theorem possibility_does_not_imply_actuality :
    Diamond allAccess sometimes false ∧ ¬ sometimes false := by
  exact ⟨⟨true, True.intro, rfl⟩, by intro h; cases h⟩

/-- Omitting contingency removes Proposition 1's prohibition. -/
theorem dropping_contingency_allows_necessitation :
    Box allAccess (fun _ : Bool => True) true ∧
    Box allAccess (fun _ : Bool => True → True) true := by
  exact ⟨fun _ _ => True.intro, fun _ _ h => h⟩

def groundExists (G : Set Unit) (p : WProp Bool) : Prop := p true ∧ G ()
def contingentHolds (_ : Unit) : WProp Bool := sometimes
def necessaryHolds (_ : Unit) (_ : Bool) : Prop := True
def impossibleHolds (_ : Unit) (_ : Bool) : Prop := False
def noGrounds (_ : Set Unit) (_ : WProp Bool) : Prop := False

theorem groundExists_psr : RestrictedPSR allAccess true allConcrete groundExists := by
  intro p _ hp _
  exact ⟨Set.univ, hp, Set.mem_univ ()⟩

/-- PSR and factivity can hold with only contingent grounds. P10 is essential. -/
theorem dropping_P10_countermodel :
    RestrictedPSR allAccess true allConcrete groundExists ∧
    GroundFactivity true contingentHolds groundExists ∧
    ¬ NoWhollyContingentGround allAccess contingentHolds true groundExists sometimes ∧
    ¬ (∃ G, groundExists G sometimes ∧
      ∃ g ∈ G, Box allAccess (contingentHolds g) true) := by
  refine ⟨groundExists_psr, ?_, ?_, ?_⟩
  · intro G p hG
    exact ⟨hG.1, fun _ _ => rfl⟩
  · intro h10
    exact h10 Set.univ (fun _ _ => sometimes_contingent)
      ⟨rfl, Set.mem_univ ()⟩
  · rintro ⟨G, _, g, _, hg⟩
    exact sometimes_not_necessary hg

/-- Brute contingent actuality: P10 and factivity hold vacuously but PSR fails.
    Together with the modal lemmas, this refutes an unconditional ground claim. -/
theorem dropping_PSR_countermodel :
    Contingent allAccess sometimes true ∧
    NoWhollyContingentGround allAccess contingentHolds true noGrounds sometimes ∧
    GroundFactivity true contingentHolds noGrounds ∧
    ¬ RestrictedPSR allAccess true allConcrete noGrounds ∧
    ¬ (∃ G, noGrounds G sometimes) := by
  refine ⟨sometimes_contingent, ?_, ?_, ?_, ?_⟩
  · intro G _ hG
    exact hG
  · intro G p hG
    exact False.elim hG
  · intro hPSR
    obtain ⟨G, hG⟩ := hPSR sometimes True.intro rfl sometimes_contingent
    exact hG
  · rintro ⟨G, hG⟩
    exact hG

/-- A non-contingent but impossible candidate is not a necessary existent.
    Without grounding factivity, PSR and P10 alone admit this countermodel. -/
theorem dropping_factivity_countermodel :
    RestrictedPSR allAccess true allConcrete groundExists ∧
    NoWhollyContingentGround allAccess impossibleHolds true groundExists sometimes ∧
    ¬ GroundFactivity true impossibleHolds groundExists ∧
    ¬ (∃ g : Unit, Box allAccess (impossibleHolds g) true) := by
  refine ⟨groundExists_psr, ?_, ?_, ?_⟩
  · intro G hwhole hG
    obtain ⟨v, _, hv⟩ := (hwhole () hG.2).1
    exact hv
  · intro hf
    exact (hf Set.univ sometimes ⟨rfl, Set.mem_univ ()⟩).2 () (Set.mem_univ ())
  · rintro ⟨g, hg⟩
    exact hg true True.intro

/-- A concrete model of all the main premises together with contingent effects.
    Hence the assumptions have an explicit model, relative to Lean's foundations.
    `groundExists` is actual explanatory grounding, not necessary implication. -/
theorem joint_premises_satisfiable :
    Box allAccess (fun _ : Bool => True) true ∧
    sometimes true ∧ Contingent allAccess sometimes true ∧
    allConcrete sometimes ∧
    RestrictedPSR allAccess true allConcrete groundExists ∧
    NoWhollyContingentGround allAccess necessaryHolds true groundExists sometimes ∧
    GroundFactivity true necessaryHolds groundExists := by
  refine ⟨(fun _ _ => True.intro), rfl, sometimes_contingent, True.intro,
    groundExists_psr, ?_, ?_⟩
  · intro G hwhole hG
    exact always_not_contingent (hwhole () hG.2)
  · intro G p hG
    exact ⟨hG.1, fun _ _ => True.intro⟩

/-- Even all premises do not entail an arbitrary extra theological attribute.
    The interpretation here makes that attribute false of every candidate. -/
theorem extra_attribute_not_entailed :
    ¬ (∃ g : Unit, Box allAccess (necessaryHolds g) true ∧
      (fun _ : Unit => False) g) := by
  rintro ⟨g, _, hg⟩
  exact hg

def mixedHolds (g w : Bool) : Prop := g = false ∨ w = true

/-- A collection can have a necessary member and a contingent joint obtaining.
    Thus Proposition 2 cannot silently be strengthened to an all-necessary ground. -/
theorem necessary_component_not_necessary_collection :
    (∃ g : Bool, g ∈ (Set.univ : Set Bool) ∧
      Box allAccess (mixedHolds g) true) ∧
    Contingent allAccess (fun w => ∀ g : Bool, mixedHolds g w) true := by
  constructor
  · exact ⟨false, Set.mem_univ false, fun _ _ => Or.inl rfl⟩
  · refine ⟨⟨true, True.intro, fun _ => Or.inr rfl⟩, false, True.intro, ?_⟩
    intro h
    have hbad := h true
    rcases hbad with hbad | hbad <;> cases hbad

def totalityGround (G : Set Bool) (p : WProp Bool) : Prop := p true ∧ G false

/-- The explicit conjunction interpretation of totality also has a joint model:
    the false-labelled entity necessarily obtains, the true-labelled entity is
    contingent, and the designated total fact collects the latter.
    This strengthens the satisfiability check beyond an uninterpreted C. -/
theorem represented_totality_premises_satisfiable :
    Contingent allAccess (TotalFact allAccess mixedHolds true) true ∧
    RestrictedPSR allAccess true allConcrete totalityGround ∧
    NoWhollyContingentGround allAccess mixedHolds true totalityGround
      (TotalFact allAccess mixedHolds true) ∧
    GroundFactivity true mixedHolds totalityGround := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply total_fact_contingent True.intro
    refine ⟨true, Or.inr rfl, ?_⟩
    refine ⟨⟨true, True.intro, Or.inr rfl⟩, false, True.intro, ?_⟩
    intro hbad
    rcases hbad with hbad | hbad <;> cases hbad
  · intro p _ hp _
    exact ⟨Set.univ, hp, Set.mem_univ false⟩
  · intro G hwhole hG
    obtain ⟨v, _, hn⟩ := (hwhole false hG.2).2
    exact hn (Or.inl rfl)
  · intro G p hG
    exact ⟨hG.1, fun _ _ => Or.inr rfl⟩

/-! ### Models for the strengthened argument
A candidate ground is a pair of flags: the first marks concreteness, the
second contingency, and a contingent candidate obtains only at `true`. So
`(true, false)` is a necessary concrete reality, `(false, false)` is
mathematics, and `(true, true)` is contingent concrete reality. -/

def itemHolds (g : Bool × Bool) (w : Bool) : Prop := g.2 = false ∨ w = true
def itemConcrete (g : Bool × Bool) : Prop := g.1 = true

/-- The contingent concrete totality of these models. -/
def worldFact : WProp Bool := itemHolds (true, true)

/-- Mathematics together with a necessary concrete reality. -/
def fullGround (G : Set (Bool × Bool)) (p : WProp Bool) : Prop :=
  p true ∧ G = {(true, false), (false, false)}

/-- Contingent concrete reality padded with mathematics. -/
def paddedGround (G : Set (Bool × Bool)) (p : WProp Bool) : Prop :=
  p true ∧ G = {(false, false), (true, true)}

/-- Mathematics alone. -/
def mathOnlyGround (G : Set (Bool × Bool)) (p : WProp Bool) : Prop :=
  p true ∧ G = {(false, false)}

/-- Contingent concrete reality alone. -/
def contingentGround (G : Set (Bool × Bool)) (p : WProp Bool) : Prop :=
  p true ∧ G = {(true, true)}

def noItemGrounds (_ : Set (Bool × Bool)) (_ : WProp Bool) : Prop := False

theorem necessary_items_not_contingent (c : Bool) :
    ¬ Contingent allAccess (itemHolds (c, false)) true := by
  rintro ⟨_, v, _, hv⟩
  exact hv (Or.inl rfl)

theorem worldFact_contingent : Contingent allAccess worldFact true := by
  refine ⟨⟨true, True.intro, Or.inr rfl⟩, false, True.intro, ?_⟩
  rintro (h | h) <;> cases h

/-- The padding loophole in the original P10: with contingent reality padded
    by mathematics, PSR, P10 and factivity hold, and the original conclusion
    is met with mathematics as the necessary member. No complete ground has
    a necessary concrete member. -/
theorem original_P10_met_by_mathematics :
    RestrictedPSR allAccess true allConcrete paddedGround ∧
    NoWhollyContingentGround allAccess itemHolds true paddedGround worldFact ∧
    GroundFactivity true itemHolds paddedGround ∧
    (∃ G, paddedGround G worldFact ∧ ∃ g ∈ G, ¬ itemConcrete g ∧
      itemHolds g true ∧ Box allAccess (itemHolds g) true) ∧
    ¬ (∃ G, paddedGround G worldFact ∧ ∃ g ∈ G, itemConcrete g ∧
      Box allAccess (itemHolds g) true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _ hp _
    exact ⟨{(false, false), (true, true)}, hp, rfl⟩
  · intro G hwhole hG
    rw [hG.2] at hwhole
    exact necessary_items_not_contingent false (hwhole (false, false) (Or.inl rfl))
  · intro G p hG
    refine ⟨hG.1, fun g hg => ?_⟩
    rw [hG.2] at hg
    rcases hg with rfl | hg
    · exact Or.inl rfl
    · obtain rfl : g = (true, true) := hg
      exact Or.inr rfl
  · exact ⟨{(false, false), (true, true)}, ⟨Or.inr rfl, rfl⟩, (false, false),
      Or.inl rfl, (by intro h; cases h), Or.inl rfl, fun _ _ => Or.inl rfl⟩
  · rintro ⟨G, hG, g, hg, hgc, hbox⟩
    rw [hG.2] at hg
    rcases hg with rfl | hg
    · cases hgc
    · obtain rfl : g = (true, true) := hg
      rcases hbox false True.intro with h | h <;> cases h

/-- All strengthened premises hold with a contingent world, so they do not
    collapse modality. The ground is mathematics together with a necessary
    concrete reality. -/
theorem strengthened_premises_satisfiable :
    Box allAccess (fun _ : Bool => True) true ∧
    worldFact true ∧ Contingent allAccess worldFact true ∧ allConcrete worldFact ∧
    RestrictedPSR allAccess true allConcrete fullGround ∧
    NoContingentMember allAccess itemHolds true fullGround worldFact ∧
    AbstractInsufficiency itemConcrete fullGround worldFact ∧
    GroundFactivity true itemHolds fullGround := by
  refine ⟨fun _ _ => True.intro, Or.inr rfl, worldFact_contingent, True.intro,
    ?_, ?_, ?_, ?_⟩
  · intro p _ hp _
    exact ⟨{(true, false), (false, false)}, hp, rfl⟩
  · intro G hG g hg
    rw [hG.2] at hg
    rcases hg with rfl | hg
    · exact necessary_items_not_contingent true
    · obtain rfl : g = (false, false) := hg
      exact necessary_items_not_contingent false
  · intro G hG
    rw [hG.2]
    exact ⟨(true, false), Or.inl rfl, rfl⟩
  · intro G p hG
    refine ⟨hG.1, fun g hg => ?_⟩
    rw [hG.2] at hg
    rcases hg with rfl | hg
    · exact Or.inl rfl
    · obtain rfl : g = (false, false) := hg
      exact Or.inl rfl

/-- Mathematics alone as the ground: PSR, P10* and factivity hold, yet no
    complete ground has a concrete member. P3* is exactly what excludes the
    claim that mathematics creates physical reality. -/
theorem dropping_AI_countermodel :
    RestrictedPSR allAccess true allConcrete mathOnlyGround ∧
    NoContingentMember allAccess itemHolds true mathOnlyGround worldFact ∧
    GroundFactivity true itemHolds mathOnlyGround ∧
    ¬ AbstractInsufficiency itemConcrete mathOnlyGround worldFact := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ hp _
    exact ⟨{(false, false)}, hp, rfl⟩
  · intro G hG g hg
    rw [hG.2] at hg
    obtain rfl : g = (false, false) := hg
    exact necessary_items_not_contingent false
  · intro G p hG
    refine ⟨hG.1, fun g hg => ?_⟩
    rw [hG.2] at hg
    obtain rfl : g = (false, false) := hg
    exact Or.inl rfl
  · intro hAI
    obtain ⟨g, hg, hgc⟩ := hAI {(false, false)} ⟨Or.inr rfl, rfl⟩
    obtain rfl : g = (false, false) := hg
    cases hgc

/-- Contingent concrete reality as the whole ground: PSR, P3* and factivity
    hold, and no complete ground has a necessary member. This is the regress
    or Hume–Edwards picture, and P10* is exactly what excludes it. -/
theorem dropping_strong_nc_countermodel :
    RestrictedPSR allAccess true allConcrete contingentGround ∧
    AbstractInsufficiency itemConcrete contingentGround worldFact ∧
    GroundFactivity true itemHolds contingentGround ∧
    ¬ NoContingentMember allAccess itemHolds true contingentGround worldFact ∧
    ¬ (∃ G, contingentGround G worldFact ∧
      ∃ g ∈ G, Box allAccess (itemHolds g) true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p _ hp _
    exact ⟨{(true, true)}, hp, rfl⟩
  · intro G hG
    rw [hG.2]
    exact ⟨(true, true), rfl, rfl⟩
  · intro G p hG
    refine ⟨hG.1, fun g hg => ?_⟩
    rw [hG.2] at hg
    obtain rfl : g = (true, true) := hg
    exact Or.inr rfl
  · intro hstrong
    exact hstrong {(true, true)} ⟨Or.inr rfl, rfl⟩ (true, true) rfl
      worldFact_contingent
  · rintro ⟨G, hG, g, hg, hbox⟩
    rw [hG.2] at hg
    obtain rfl : g = (true, true) := hg
    rcases hbox false True.intro with h | h <;> cases h

/-- Brute contingent actuality: P10*, P3* and factivity hold vacuously, the
    world is contingent, and nothing grounds it. -/
theorem dropping_PSR_strong_countermodel :
    Contingent allAccess worldFact true ∧
    NoContingentMember allAccess itemHolds true noItemGrounds worldFact ∧
    AbstractInsufficiency itemConcrete noItemGrounds worldFact ∧
    GroundFactivity true itemHolds noItemGrounds ∧
    ¬ RestrictedPSR allAccess true allConcrete noItemGrounds := by
  refine ⟨worldFact_contingent, fun _ h => False.elim h, fun _ h => False.elim h,
    fun _ _ h => False.elim h, ?_⟩
  intro hPSR
  obtain ⟨_, h⟩ := hPSR worldFact True.intro (Or.inr rfl) worldFact_contingent
  exact h

/-- Nothing in the strengthened argument makes the necessary concrete member
    personal. Under one reading of an arbitrary further attribute, every
    premise and the conclusion hold while no member of any complete ground has
    the attribute, so the member can be read as an impersonal reality such as
    a necessary initial physical state. -/
theorem strengthened_ground_need_not_be_personal :
    ∃ personal : Bool × Bool → Prop,
      RestrictedPSR allAccess true allConcrete fullGround ∧
      NoContingentMember allAccess itemHolds true fullGround worldFact ∧
      AbstractInsufficiency itemConcrete fullGround worldFact ∧
      GroundFactivity true itemHolds fullGround ∧
      (∃ G, fullGround G worldFact ∧ ∃ g ∈ G, itemConcrete g ∧
        Box allAccess (itemHolds g) true) ∧
      ∀ G, fullGround G worldFact → ∀ g ∈ G, ¬ personal g := by
  obtain ⟨_, _, _, _, hPSR, hstrong, hAI, hfact⟩ := strengthened_premises_satisfiable
  exact ⟨fun _ => False, hPSR, hstrong, hAI, hfact,
    ⟨{(true, false), (false, false)}, ⟨Or.inr rfl, rfl⟩, (true, false), Or.inl rfl,
      rfl, fun _ _ => Or.inl rfl⟩,
    fun _ _ _ _ h => h⟩

end Models

/-! ## Deriving the strengthened premises

P10* and P3* are close to the conclusion they support. This part replaces
each by finer premises and proves it from them.

* P10* follows from irreflexivity of ground together with dissectivity: a
  complete ground of the totality also grounds the obtaining of each of its
  own contingent members, since that obtaining belongs to the totality.
* P3* follows from a production principle together with the inertness of
  abstract entities. The step uses the modal core: a ground whose members are
  all necessary cannot necessitate a contingent fact, so it can explain that
  fact only through productive power.

A third section indexes grounding to evaluations. The fact that `G` grounds
`C` is then itself contingent, and applying PSR to it starts a regress in
which no level explains why `C` obtains rather than fails.
-/

section Derived

variable {World : Type u} {Entity : Type v}

/-- Irreflexivity of ground: no collection grounds the obtaining of one of
    its own members. Every member of a ground is taken to contribute, so a
    ground containing `g` would use `g` to explain `g`. -/
def GroundIrreflexive (holds : Entity → WProp World)
    (grounds : Set Entity → WProp World → Prop) : Prop :=
  ∀ G, ∀ g ∈ G, ¬ grounds G (holds g)

/-- Dissectivity for `C`: a complete ground of the totality also grounds the
    obtaining of each contingent member of that ground. This is the article's
    rationale for P10, that such a member's "own actuality remains within what
    was to be explained", stated as a premise. A regress theorist denies it:
    each member is explained by other members, never by the whole ground. -/
def Dissective (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World)
    (grounds : Set Entity → WProp World → Prop) (C : WProp World) : Prop :=
  ∀ G, grounds G C → ∀ g ∈ G, Contingent R (holds g) w → grounds G (holds g)

/-- For the conjunction model of the totality: a complete ground of the total
    fact grounds each of its conjuncts. -/
def GroundsConjuncts (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World)
    (grounds : Set Entity → WProp World → Prop) : Prop :=
  ∀ G, grounds G (TotalFact R holds w) →
    ∀ e, holds e w → Contingent R (holds e) w → grounds G (holds e)

variable {R : World → World → Prop} {holds : Entity → WProp World}
variable {w : World} {grounds : Set Entity → WProp World → Prop}
variable {concrete : WProp World → Prop} {concreteE : Entity → Prop}
variable {productive : Entity → Prop} {C : WProp World}

/-- P10* is a theorem of irreflexivity and dissectivity. -/
theorem ultimacy_of_irreflexive_dissective
    (hirr : GroundIrreflexive holds grounds)
    (hdis : Dissective R holds w grounds C) :
    NoContingentMember R holds w grounds C := by
  intro G hG g hg hc
  exact hirr G g hg (hdis G hG g hg hc)

/-- In the conjunction model, dissectivity follows from grounding of
    conjuncts and factivity: a contingent member of an actual ground is an
    actual contingent fact, hence a conjunct of the total fact. -/
theorem total_fact_dissective
    (hconj : GroundsConjuncts R holds w grounds)
    (hfactive : GroundFactivity w holds grounds) :
    Dissective R holds w grounds (TotalFact R holds w) := by
  intro G hG g hg hc
  exact hconj G hG g ((hfactive G _ hG).2 g hg) hc

/-- Hence P10* holds for the represented total fact without being assumed. -/
theorem total_fact_ultimacy
    (hirr : GroundIrreflexive holds grounds)
    (hconj : GroundsConjuncts R holds w grounds)
    (hfactive : GroundFactivity w holds grounds) :
    NoContingentMember R holds w grounds (TotalFact R holds w) :=
  ultimacy_of_irreflexive_dissective hirr (total_fact_dissective hconj hfactive)

/-- Production principle: a complete ground that does not necessitate what
    it grounds has a member with productive power. Explanation without
    entailment is taken to need something that brings its effect about, as a
    chancy process or an agent does. -/
def NonNecessitatingGroundsProduce (R : World → World → Prop)
    (holds : Entity → WProp World) (w : World)
    (productive : Entity → Prop)
    (grounds : Set Entity → WProp World → Prop) : Prop :=
  ∀ G p, grounds G p →
    ¬ Box R (fun v => (∀ g ∈ G, holds g v) → p v) w → ∃ g ∈ G, productive g

/-- The modal core for collections: necessarily obtaining members cannot
    jointly necessitate a contingent fact. -/
theorem necessary_collection_does_not_necessitate
    {G : Set Entity} (hnec : ∀ g ∈ G, Box R (holds g) w)
    (hCcont : Contingent R C w) :
    ¬ Box R (fun v => (∀ g ∈ G, holds g v) → C v) w := by
  intro hbox
  obtain ⟨v, hv, hnC⟩ := hCcont.2
  exact hnC (hbox v hv (fun g hg => hnec g hg v hv))

/-- A collection of necessary, unproductive entities grounds no contingent
    fact. Neither PSR, ultimacy, nor abstract insufficiency is used. -/
theorem inert_necessities_cannot_ground
    (hCcont : Contingent R C w)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    {G : Set Entity} (hnec : ∀ g ∈ G, Box R (holds g) w)
    (hinert : ∀ g ∈ G, ¬ productive g) : ¬ grounds G C := by
  intro hG
  obtain ⟨g, hg, hp⟩ :=
    hPP G C hG (necessary_collection_does_not_necessitate hnec hCcont)
  exact hinert g hg hp

/-- Mathematics alone cannot ground contingent actuality. The premises are
    P2 and P4, the production principle, and the inertness of mathematical
    entities. The modal core does the work: mathematics cannot necessitate
    `C`, and it has no other way to explain it. -/
theorem mathematics_alone_cannot_ground
    {mathematical : Entity → Prop}
    (hmathNec : ∀ g, mathematical g → Box R (holds g) w)
    (hmathInert : ∀ g, mathematical g → ¬ productive g)
    (hCcont : Contingent R C w)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    {G : Set Entity} (hGmath : ∀ g ∈ G, mathematical g) : ¬ grounds G C :=
  inert_necessities_cannot_ground hCcont hPP
    (fun g hg => hmathNec g (hGmath g hg))
    (fun g hg => hmathInert g (hGmath g hg))

/-- Under ultimacy, every complete ground of a contingent `C` has a
    productive member, because it does not necessitate `C`. -/
theorem productive_member_of_ultimate_ground
    (hrefl : R w w) (hCcont : Contingent R C w)
    (hstrong : NoContingentMember R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    {G : Set Entity} (hG : grounds G C) : ∃ g ∈ G, productive g :=
  hPP G C hG (ground_does_not_necessitate hrefl hCcont hstrong hfactive hG)

/-- P3* is a theorem of the production principle and the inertness of
    abstract entities, here in the form that whatever is productive is
    concrete. -/
theorem abstract_insufficiency_of_production
    (hrefl : R w w) (hCcont : Contingent R C w)
    (hstrong : NoContingentMember R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    (hinert : ∀ g, productive g → concreteE g) :
    AbstractInsufficiency concreteE grounds C := by
  intro G hG
  obtain ⟨g, hg, hp⟩ :=
    productive_member_of_ultimate_ground hrefl hCcont hstrong hfactive hPP hG
  exact ⟨g, hg, hinert g hp⟩

/-- Some complete ground of `C` has a member that is productive, concrete,
    and necessarily existing. Causal power is no longer left open. -/
theorem necessary_productive_ground
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (hstrong : NoContingentMember R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    (hinert : ∀ g, productive g → concreteE g) :
    ∃ G, grounds G C ∧
      ∃ g ∈ G, productive g ∧ concreteE g ∧ holds g w ∧ Box R (holds g) w := by
  obtain ⟨G, hG⟩ := hPSR C hCconcrete hCactual hCcont
  obtain ⟨g, hg, hp⟩ :=
    productive_member_of_ultimate_ground hrefl hCcont hstrong hfactive hPP hG
  have hactual := (hfactive G C hG).2 g hg
  exact ⟨G, hG, g, hg, hp, hinert g hp, hactual,
    necessary_of_actual_noncontingent hrefl hactual (hstrong G hG g hg)⟩

/-- The argument with P10* and P3* derived, not assumed. From contingency,
    PSR-A, irreflexivity, dissectivity, factivity, the production principle,
    and inertness: mathematics alone does not necessitate `C`, some complete
    ground of `C` has a productive, concrete, necessarily existing member,
    and that ground does not necessitate `C`. -/
theorem derived_argument
    {N : WProp World} (hN : Box R N w)
    (hrefl : R w w) (hCactual : C w) (hCcont : Contingent R C w)
    (hCconcrete : concrete C)
    (hPSR : RestrictedPSR R w concrete grounds)
    (hirr : GroundIrreflexive holds grounds)
    (hdis : Dissective R holds w grounds C)
    (hfactive : GroundFactivity w holds grounds)
    (hPP : NonNecessitatingGroundsProduce R holds w productive grounds)
    (hinert : ∀ g, productive g → concreteE g) :
    (¬ Box R (fun v => N v → C v) w) ∧
    ∃ G, grounds G C ∧
      (∃ g ∈ G, productive g ∧ concreteE g ∧ holds g w ∧ Box R (holds g) w) ∧
      ¬ Box R (fun v => (∀ g ∈ G, holds g v) → C v) w := by
  have hstrong := ultimacy_of_irreflexive_dissective hirr hdis
  obtain ⟨G, hG⟩ := hPSR C hCconcrete hCactual hCcont
  obtain ⟨g, hg, hp⟩ :=
    productive_member_of_ultimate_ground hrefl hCcont hstrong hfactive hPP hG
  have hactual := (hfactive G C hG).2 g hg
  exact ⟨modal_non_selection hN hCcont, G, hG,
    ⟨g, hg, hp, hinert g hp, hactual,
      necessary_of_actual_noncontingent hrefl hactual (hstrong G hG g hg)⟩,
    ground_does_not_necessitate hrefl hCcont hstrong hfactive hG⟩

end Derived

/-! ## Grounding indexed to evaluations

So far `grounds G C` has been a single fact about the actual evaluation.
Here `groundsAt v G p` says that `G` grounds `p` at `v`, so the grounding
fact `fun v => groundsAt v G C` is a proposition like any other.
-/

section Indexed

variable {World : Type u} {Entity : Type v}

/-- Factivity at every accessible evaluation. -/
def FactiveAt (R : World → World → Prop) (w : World)
    (holds : Entity → WProp World)
    (groundsAt : World → Set Entity → WProp World → Prop) : Prop :=
  ∀ v, R w v → ∀ G p, groundsAt v G p → p v ∧ ∀ g ∈ G, holds g v

/-- The hierarchy of grounding facts over `C`. Level 0 is `C`; a fact of
    level `n + 1` says that some `G` grounds a fact of level `n` which it
    actually grounds. -/
inductive GroundingLevel
    (groundsAt : World → Set Entity → WProp World → Prop)
    (w : World) (C : WProp World) : Nat → WProp World → Prop
  | base : GroundingLevel groundsAt w C 0 C
  | step {n : Nat} {p : WProp World} {G : Set Entity} :
      GroundingLevel groundsAt w C n p → groundsAt w G p →
      GroundingLevel groundsAt w C (n + 1) (fun v => groundsAt v G p)

variable {R : World → World → Prop} {holds : Entity → WProp World}
variable {w : World} {groundsAt : World → Set Entity → WProp World → Prop}
variable {concrete : WProp World → Prop} {C : WProp World}

/-- Van Inwagen's lemma. Whatever actually obtains and necessitates a
    contingent fact is itself contingent. So anything that settles why `C`
    obtains rather than fails, such as a choice or a chance outcome, is a
    contingent fact, and by ultimacy lies outside the ultimate ground. -/
theorem necessitating_fact_is_contingent {q : WProp World}
    (hrefl : R w w) (hq : q w)
    (hnec : Box R (fun v => q v → C v) w) (hCcont : Contingent R C w) :
    Contingent R q w := by
  obtain ⟨v, hv, hnC⟩ := hCcont.2
  exact ⟨⟨w, hrefl, hq⟩, v, hv, fun hqv => hnC (hnec v hv hqv)⟩

/-- By factivity, the grounding fact necessitates what is grounded. -/
theorem grounding_fact_necessitates
    (hf : FactiveAt R w holds groundsAt) (G : Set Entity) :
    Box R (fun v => groundsAt v G C → C v) w := by
  intro v hv hG
  exact (hf v hv G C hG).1

/-- The fact that `G` grounds a contingent `C` is itself contingent,
    whatever `G` is. No ultimacy premise is used. -/
theorem grounding_fact_contingent
    (hrefl : R w w) (hf : FactiveAt R w holds groundsAt)
    (hCcont : Contingent R C w) {G : Set Entity} (hG : groundsAt w G C) :
    Contingent R (fun v => groundsAt v G C) w :=
  necessitating_fact_is_contingent (q := fun v => groundsAt v G C)
    hrefl hG (grounding_fact_necessitates hf G) hCcont

/-- Under ultimacy there is an accessible evaluation at which every member
    of the ground obtains and yet the ground does not ground `C`. The
    difference between that evaluation and the actual one lies wholly in the
    grounding fact, not in the ground. -/
theorem ground_obtains_without_grounding
    (hrefl : R w w) (hCcont : Contingent R C w)
    (hstrong : NoContingentMember R holds w (groundsAt w) C)
    (hf : FactiveAt R w holds groundsAt)
    {G : Set Entity} (hG : groundsAt w G C) :
    ∃ v, R w v ∧ (∀ g ∈ G, holds g v) ∧ ¬ groundsAt v G C := by
  obtain ⟨v, hv, hnC, hall⟩ :=
    ground_obtains_where_C_fails hrefl hCcont hstrong (hf w hrefl) hG
  exact ⟨v, hv, hall, fun hGv => hnC (hf v hv G C hGv).1⟩

/-- Every fact in the hierarchy actually obtains and is contingent. -/
theorem grounding_level_contingent
    (hrefl : R w w) (hf : FactiveAt R w holds groundsAt)
    (hCactual : C w) (hCcont : Contingent R C w)
    {n : Nat} {p : WProp World} (h : GroundingLevel groundsAt w C n p) :
    p w ∧ Contingent R p w := by
  induction h with
  | base => exact ⟨hCactual, hCcont⟩
  | step _ hG ih => exact ⟨hG, grounding_fact_contingent hrefl hf ih.2 hG⟩

/-- The regress. If grounding facts fall under PSR, the hierarchy has a
    grounded, actual, contingent fact at every level. Propositions here are
    individuated by the evaluations at which they hold, so the levels need
    not be distinct facts; the regress may be a fixed point. -/
theorem grounding_regress
    (hrefl : R w w) (hf : FactiveAt R w holds groundsAt)
    (hPSR : RestrictedPSR R w concrete (groundsAt w))
    (hclosed : ∀ G p, concrete p → concrete (fun v => groundsAt v G p))
    (hCactual : C w) (hCcont : Contingent R C w) (hCconcrete : concrete C) :
    ∀ n, ∃ p, GroundingLevel groundsAt w C n p ∧ concrete p ∧
      p w ∧ Contingent R p w := by
  intro n
  induction n with
  | zero => exact ⟨C, .base, hCconcrete, hCactual, hCcont⟩
  | succ n ih =>
    obtain ⟨p, hlevel, hpc, hpw, hpcont⟩ := ih
    obtain ⟨G, hG⟩ := hPSR p hpc hpw hpcont
    exact ⟨fun v => groundsAt v G p, .step hlevel hG, hclosed G p hpc, hG,
      grounding_fact_contingent hrefl hf hpcont hG⟩

/-- If ultimacy holds at every level, no level settles the contrast: each
    ground still obtains at an accessible evaluation where the fact it
    grounds fails. Ascending the hierarchy never yields an explanation of
    why `C` obtains rather than fails. -/
theorem no_level_settles_the_contrast
    (hrefl : R w w) (hf : FactiveAt R w holds groundsAt)
    (hCactual : C w) (hCcont : Contingent R C w)
    (hult : ∀ n p, GroundingLevel groundsAt w C n p →
      NoContingentMember R holds w (groundsAt w) p)
    {n : Nat} {p : WProp World} {G : Set Entity}
    (hlevel : GroundingLevel groundsAt w C n p) (hG : groundsAt w G p) :
    ∃ v, R w v ∧ ¬ p v ∧ ∀ g ∈ G, holds g v :=
  ground_obtains_where_C_fails hrefl
    (grounding_level_contingent hrefl hf hCactual hCcont hlevel).2
    (hult n p hlevel) (hf w hrefl) hG

end Indexed

/-! ## Models for the derived premises -/

namespace Models

/-! ### Two premises whose necessity was not yet shown -/

/-- Three evaluations. The actual one, `none`, accesses the other two but
    not itself. -/
def noSelfAccess (_ v : Option Bool) : Prop := v ≠ none
def actualOnly (_ : Unit) (w : Option Bool) : Prop := w = none
def openFact (w : Option Bool) : Prop := w ≠ some false
def actualGround (G : Set Unit) (p : WProp (Option Bool)) : Prop := p none ∧ G ()

/-- Self-access is essential. Without it every other premise of
    `necessary_concrete_ground` holds, the one candidate obtains only at the
    actual evaluation, and so is non-contingent without being necessary. -/
theorem dropping_self_access_countermodel :
    ¬ noSelfAccess none none ∧
    openFact none ∧ Contingent noSelfAccess openFact none ∧
    RestrictedPSR noSelfAccess none (fun _ => True) actualGround ∧
    NoContingentMember noSelfAccess actualOnly none actualGround openFact ∧
    AbstractInsufficiency (fun _ : Unit => True) actualGround openFact ∧
    GroundFactivity none actualOnly actualGround ∧
    ¬ (∃ G, actualGround G openFact ∧
      ∃ g ∈ G, Box noSelfAccess (actualOnly g) none) := by
  have hopen : openFact none := by intro h; cases h
  have hacc : noSelfAccess none (some true) := by intro h; cases h
  refine ⟨fun h => h rfl, hopen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨⟨some true, hacc, by intro h; cases h⟩,
      some false, (by intro h; cases h), fun h => h rfl⟩
  · intro p _ hp _
    exact ⟨Set.univ, hp, Set.mem_univ ()⟩
  · intro G _ g _ hc
    obtain ⟨v, hv, hg⟩ := hc.1
    exact hv hg
  · intro G hG
    exact ⟨(), hG.2, True.intro⟩
  · intro G p hG
    exact ⟨hG.1, fun _ _ => rfl⟩
  · rintro ⟨G, _, g, _, hbox⟩
    have hbad := hbox (some true) hacc
    cases hbad

/-- Factivity is essential to the strengthened argument too. An impossible
    concrete candidate satisfies PSR, P10* and P3*, and nothing necessary
    exists. -/
theorem dropping_factivity_strong_countermodel :
    RestrictedPSR allAccess true allConcrete groundExists ∧
    NoContingentMember allAccess impossibleHolds true groundExists sometimes ∧
    AbstractInsufficiency (fun _ : Unit => True) groundExists sometimes ∧
    ¬ GroundFactivity true impossibleHolds groundExists ∧
    ¬ (∃ g : Unit, Box allAccess (impossibleHolds g) true) := by
  refine ⟨groundExists_psr, ?_, ?_, ?_, ?_⟩
  · intro G _ g _ hc
    obtain ⟨v, _, hv⟩ := hc.1
    exact hv
  · intro G hG
    exact ⟨(), hG.2, True.intro⟩
  · intro hf
    exact (hf Set.univ sometimes ⟨rfl, Set.mem_univ ()⟩).2 () (Set.mem_univ ())
  · rintro ⟨g, hg⟩
    exact hg true True.intro

/-! ### Irreflexivity, dissectivity, production -/

/-- The joint model of the strengthened premises is not irreflexive: there
    the same collection grounds every actual truth, including the obtaining
    of its own members. A stricter model is needed. -/
theorem fullGround_not_irreflexive : ¬ GroundIrreflexive itemHolds fullGround := by
  intro h
  exact h {(true, false), (false, false)} (true, false) (Or.inl rfl)
    ⟨Or.inl rfl, rfl⟩

/-- Grounding indexed to evaluations. Only facts that fail at `false`, the
    contingent ones, are grounded, and they are grounded by mathematics
    together with a necessary concrete reality. -/
def strictGroundAt (v : Bool) (G : Set (Bool × Bool)) (p : WProp Bool) : Prop :=
  p v ∧ ¬ p false ∧ G = {(true, false), (false, false)}

theorem strictGround_psr :
    RestrictedPSR allAccess true allConcrete (strictGroundAt true) := by
  intro p _ hp hc
  obtain ⟨v, _, hnp⟩ := hc.2
  have hpf : ¬ p false := by
    cases v with
    | false => exact hnp
    | true => exact absurd hp hnp
  exact ⟨{(true, false), (false, false)}, hp, hpf, rfl⟩

theorem strictGround_factive : FactiveAt allAccess true itemHolds strictGroundAt := by
  intro v _ G p hG
  refine ⟨hG.1, fun g hg => ?_⟩
  rw [hG.2.2] at hg
  rcases hg with rfl | hg
  · exact Or.inl rfl
  · obtain rfl : g = (false, false) := hg
    exact Or.inl rfl

/-- In this model ultimacy holds for every grounded fact, not only for the
    totality. -/
theorem strictGround_members_necessary (p : WProp Bool) :
    NoContingentMember allAccess itemHolds true (strictGroundAt true) p := by
  intro G hG g hg
  rw [hG.2.2] at hg
  rcases hg with rfl | hg
  · exact necessary_items_not_contingent true
  · obtain rfl : g = (false, false) := hg
    exact necessary_items_not_contingent false

/-- The premises of `derived_argument` hold together with a contingent
    world. Productive power is read as concreteness, so mathematics is inert
    and still belongs to the ground. -/
theorem derived_premises_satisfiable :
    Box allAccess (fun _ : Bool => True) true ∧
    worldFact true ∧ Contingent allAccess worldFact true ∧ allConcrete worldFact ∧
    RestrictedPSR allAccess true allConcrete (strictGroundAt true) ∧
    GroundIrreflexive itemHolds (strictGroundAt true) ∧
    Dissective allAccess itemHolds true (strictGroundAt true) worldFact ∧
    GroundFactivity true itemHolds (strictGroundAt true) ∧
    NonNecessitatingGroundsProduce allAccess itemHolds true itemConcrete
      (strictGroundAt true) := by
  refine ⟨fun _ _ => True.intro, Or.inr rfl, worldFact_contingent, True.intro,
    strictGround_psr, ?_, ?_, strictGround_factive true True.intro, ?_⟩
  · intro G g hg hgr
    obtain ⟨_, hnf, hGeq⟩ := hgr
    rw [hGeq] at hg
    rcases hg with rfl | hg
    · exact hnf (Or.inl rfl)
    · obtain rfl : g = (false, false) := hg
      exact hnf (Or.inl rfl)
  · intro G hG g hg hc
    exact absurd hc (strictGround_members_necessary worldFact G hG g hg)
  · intro G p hG _
    rw [hG.2.2]
    exact ⟨(true, false), Or.inl rfl, rfl⟩

/-- The premises of `grounding_regress` and `no_level_settles_the_contrast`
    hold together: the world is actually grounded, grounding is factive at
    every evaluation, PSR covers every actual contingent fact including
    grounding facts, and ultimacy holds at every level. The regress is
    therefore consistent. It is not vicious, and it is not an explanation of
    the contrast either. -/
theorem indexed_premises_satisfiable :
    strictGroundAt true {(true, false), (false, false)} worldFact ∧
    FactiveAt allAccess true itemHolds strictGroundAt ∧
    RestrictedPSR allAccess true allConcrete (strictGroundAt true) ∧
    (∀ G p, allConcrete p → allConcrete (fun v => strictGroundAt v G p)) ∧
    (∀ p, NoContingentMember allAccess itemHolds true (strictGroundAt true) p) := by
  refine ⟨⟨Or.inr rfl, ?_, rfl⟩, strictGround_factive, strictGround_psr,
    fun _ _ _ => True.intro, strictGround_members_necessary⟩
  rintro (h | h) <;> cases h

/-- Irreflexivity is essential. If a contingent reality may ground the
    obtaining of itself, dissectivity holds, P10* fails, and no complete
    ground has a necessary member. -/
theorem dropping_irreflexivity_countermodel :
    RestrictedPSR allAccess true allConcrete contingentGround ∧
    Dissective allAccess itemHolds true contingentGround worldFact ∧
    GroundFactivity true itemHolds contingentGround ∧
    ¬ GroundIrreflexive itemHolds contingentGround ∧
    ¬ NoContingentMember allAccess itemHolds true contingentGround worldFact ∧
    ¬ (∃ G, contingentGround G worldFact ∧
      ∃ g ∈ G, Box allAccess (itemHolds g) true) := by
  obtain ⟨hPSR, _, hfact, hnstrong, hnone⟩ := dropping_strong_nc_countermodel
  refine ⟨hPSR, ?_, hfact, ?_, hnstrong, hnone⟩
  · intro G hG g hg _
    rw [hG.2] at hg
    obtain rfl : g = (true, true) := hg
    exact ⟨Or.inr rfl, hG.2⟩
  · intro hirr
    exact hirr {(true, true)} (true, true) rfl ⟨Or.inr rfl, rfl⟩

/-- Four evaluations and two independent contingent realities, one for each
    coordinate. -/
def pairAccess (_ _ : Bool × Bool) : Prop := True
def pairHolds (g : Bool) (w : Bool × Bool) : Prop := (bif g then w.1 else w.2) = true
def bothFact (w : Bool × Bool) : Prop := w.1 = true ∧ w.2 = true

/-- The facts that fail whenever either reality is absent. -/
def wholeOnly (p : WProp (Bool × Bool)) : Prop :=
  ¬ p (true, false) ∧ ¬ p (false, true)

/-- Both realities together ground the whole, and nothing grounds a part. -/
def wholeOnlyGround (G : Set Bool) (p : WProp (Bool × Bool)) : Prop :=
  p (true, true) ∧ wholeOnly p ∧ G = Set.univ

/-- Dissectivity is essential. Two contingent realities ground their joint
    obtaining, ground is irreflexive and factive, and no complete ground has
    a necessary member. This is the regress theorist's picture: the whole is
    explained by its members, and no member is explained by the whole. -/
theorem dropping_dissectivity_countermodel :
    bothFact (true, true) ∧ Contingent pairAccess bothFact (true, true) ∧
    wholeOnly bothFact ∧
    RestrictedPSR pairAccess (true, true) wholeOnly wholeOnlyGround ∧
    GroundIrreflexive pairHolds wholeOnlyGround ∧
    GroundFactivity (true, true) pairHolds wholeOnlyGround ∧
    ¬ Dissective pairAccess pairHolds (true, true) wholeOnlyGround bothFact ∧
    ¬ NoContingentMember pairAccess pairHolds (true, true) wholeOnlyGround bothFact ∧
    ¬ (∃ G, wholeOnlyGround G bothFact ∧
      ∃ g ∈ G, Box pairAccess (pairHolds g) (true, true)) := by
  have hfirst : ¬ bothFact (true, false) := fun h => Bool.false_ne_true h.2
  have hsecond : ¬ bothFact (false, true) := fun h => Bool.false_ne_true h.1
  have hwhole : wholeOnly bothFact := ⟨hfirst, hsecond⟩
  have hground : wholeOnlyGround Set.univ bothFact := ⟨⟨rfl, rfl⟩, hwhole, rfl⟩
  have hcont : Contingent pairAccess (pairHolds true) (true, true) :=
    ⟨⟨(true, true), True.intro, rfl⟩, (false, true), True.intro,
      fun h => Bool.false_ne_true h⟩
  refine ⟨⟨rfl, rfl⟩, ⟨⟨(true, true), True.intro, rfl, rfl⟩,
    (true, false), True.intro, hfirst⟩, hwhole, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hpw _
    exact ⟨Set.univ, hpw, hp, rfl⟩
  · intro G g _ hgr
    cases g with
    | true => exact hgr.2.1.1 rfl
    | false => exact hgr.2.1.2 rfl
  · intro G p hG
    exact ⟨hG.1, fun g _ => by cases g <;> rfl⟩
  · intro hdis
    exact (hdis Set.univ hground true (Set.mem_univ true) hcont).2.1.1 rfl
  · intro hstrong
    exact hstrong Set.univ hground true (Set.mem_univ true) hcont
  · rintro ⟨G, _, g, _, hbox⟩
    cases g with
    | true => exact Bool.false_ne_true (hbox (false, true) True.intro)
    | false => exact Bool.false_ne_true (hbox (true, false) True.intro)

/-- The production principle is essential. Without it, mathematics alone
    grounds the world although it is necessary, unproductive, and does not
    necessitate the world. -/
theorem dropping_production_countermodel :
    Contingent allAccess worldFact true ∧
    Box allAccess (itemHolds (false, false)) true ∧
    ¬ itemConcrete (false, false) ∧
    mathOnlyGround {(false, false)} worldFact ∧
    ¬ NonNecessitatingGroundsProduce allAccess itemHolds true itemConcrete
      mathOnlyGround := by
  have hG : mathOnlyGround {(false, false)} worldFact := ⟨Or.inr rfl, rfl⟩
  refine ⟨worldFact_contingent, fun _ _ => Or.inl rfl, (by intro h; cases h), hG, ?_⟩
  intro hPP
  have hmembers : ∀ g ∈ ({(false, false)} : Set (Bool × Bool)),
      Box allAccess (itemHolds g) true := by
    intro g hg
    obtain rfl : g = (false, false) := hg
    exact fun _ _ => Or.inl rfl
  obtain ⟨g, hg, hp⟩ := hPP {(false, false)} worldFact hG
    (necessary_collection_does_not_necessitate hmembers worldFact_contingent)
  obtain rfl : g = (false, false) := hg
  cases hp

/-- Inertness is essential. If mathematics counts as productive, the
    production principle holds and mathematics alone grounds the world. -/
theorem dropping_inertness_countermodel :
    NonNecessitatingGroundsProduce allAccess itemHolds true (fun _ => True)
      mathOnlyGround ∧
    mathOnlyGround {(false, false)} worldFact ∧
    ¬ (∀ g : Bool × Bool, (fun _ => True) g → itemConcrete g) := by
  refine ⟨?_, ⟨Or.inr rfl, rfl⟩, ?_⟩
  · intro G p hG _
    rw [hG.2]
    exact ⟨(false, false), rfl, True.intro⟩
  · intro h
    have hbad := h (false, false) True.intro
    cases hbad

end Models

end ActualityGround

/-! Kernel dependency audit. These commands expose foundational dependencies
and any accidental admitted proof dependency in the actual compilation output. -/
#print axioms ActualityGround.box_modus_ponens
#print axioms ActualityGround.contingent_not_necessary
#print axioms ActualityGround.modal_non_selection
#print axioms ActualityGround.necessary_ground_cannot_necessitate_contingent_effect
#print axioms ActualityGround.necessary_of_actual_noncontingent
#print axioms ActualityGround.noncontingent_component_of_complete_ground
#print axioms ActualityGround.noncontingent_ground_consequence
#print axioms ActualityGround.necessary_ground_consequence
#print axioms ActualityGround.refined_argument
#print axioms ActualityGround.total_fact_actual
#print axioms ActualityGround.total_fact_contingent
#print axioms ActualityGround.represented_totality_necessary_ground
#print axioms ActualityGround.Models.sometimes_contingent
#print axioms ActualityGround.Models.sometimes_not_necessary
#print axioms ActualityGround.Models.always_not_contingent
#print axioms ActualityGround.Models.possibility_does_not_imply_actuality
#print axioms ActualityGround.Models.dropping_contingency_allows_necessitation
#print axioms ActualityGround.Models.groundExists_psr
#print axioms ActualityGround.Models.dropping_P10_countermodel
#print axioms ActualityGround.Models.dropping_PSR_countermodel
#print axioms ActualityGround.Models.dropping_factivity_countermodel
#print axioms ActualityGround.Models.joint_premises_satisfiable
#print axioms ActualityGround.Models.extra_attribute_not_entailed
#print axioms ActualityGround.Models.necessary_component_not_necessary_collection
#print axioms ActualityGround.Models.represented_totality_premises_satisfiable
#print axioms ActualityGround.strengthened_premises_imply_P10
#print axioms ActualityGround.necessary_concrete_ground
#print axioms ActualityGround.ground_obtains_where_C_fails
#print axioms ActualityGround.ground_does_not_necessitate
#print axioms ActualityGround.brute_fact_or_noncontingent_concretum
#print axioms ActualityGround.abstract_necessity_alone_cannot_ground
#print axioms ActualityGround.strengthened_argument
#print axioms ActualityGround.Models.necessary_items_not_contingent
#print axioms ActualityGround.Models.worldFact_contingent
#print axioms ActualityGround.Models.original_P10_met_by_mathematics
#print axioms ActualityGround.Models.strengthened_premises_satisfiable
#print axioms ActualityGround.Models.dropping_AI_countermodel
#print axioms ActualityGround.Models.dropping_strong_nc_countermodel
#print axioms ActualityGround.Models.dropping_PSR_strong_countermodel
#print axioms ActualityGround.Models.strengthened_ground_need_not_be_personal
#print axioms ActualityGround.ultimacy_of_irreflexive_dissective
#print axioms ActualityGround.total_fact_dissective
#print axioms ActualityGround.total_fact_ultimacy
#print axioms ActualityGround.necessary_collection_does_not_necessitate
#print axioms ActualityGround.inert_necessities_cannot_ground
#print axioms ActualityGround.mathematics_alone_cannot_ground
#print axioms ActualityGround.productive_member_of_ultimate_ground
#print axioms ActualityGround.abstract_insufficiency_of_production
#print axioms ActualityGround.necessary_productive_ground
#print axioms ActualityGround.derived_argument
#print axioms ActualityGround.necessitating_fact_is_contingent
#print axioms ActualityGround.grounding_fact_necessitates
#print axioms ActualityGround.grounding_fact_contingent
#print axioms ActualityGround.ground_obtains_without_grounding
#print axioms ActualityGround.grounding_level_contingent
#print axioms ActualityGround.grounding_regress
#print axioms ActualityGround.no_level_settles_the_contrast
#print axioms ActualityGround.Models.dropping_self_access_countermodel
#print axioms ActualityGround.Models.dropping_factivity_strong_countermodel
#print axioms ActualityGround.Models.fullGround_not_irreflexive
#print axioms ActualityGround.Models.strictGround_psr
#print axioms ActualityGround.Models.strictGround_factive
#print axioms ActualityGround.Models.strictGround_members_necessary
#print axioms ActualityGround.Models.derived_premises_satisfiable
#print axioms ActualityGround.Models.indexed_premises_satisfiable
#print axioms ActualityGround.Models.dropping_irreflexivity_countermodel
#print axioms ActualityGround.Models.dropping_dissectivity_countermodel
#print axioms ActualityGround.Models.dropping_production_countermodel
#print axioms ActualityGround.Models.dropping_inertness_countermodel
