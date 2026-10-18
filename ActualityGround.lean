import Mathlib.Data.Set.Basic

/-!
# From Mathematical Possibility to Actuality: a conditional formalization

Source: `actuality_and_necessary_ground.pdf`, 20 September 2026, 16 pages.
The formal targets are Proposition 1 (p. 5), Proposition 2 (p. 6),
the twelve steps (p. 12), and the modal-collapse objection (p. 10).

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
