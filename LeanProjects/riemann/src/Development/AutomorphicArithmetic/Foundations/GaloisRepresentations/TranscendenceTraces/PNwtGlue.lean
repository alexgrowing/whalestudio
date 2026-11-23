import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem lift_ex {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) [IsOpenImmersion A.u] {Ω : Type} [Field Ω]
    (z : gp Ω ⟶ Z) (hz : pt (z ≫ p) ∈ Set.range A.u) : ∃ l : gp Ω ⟶ A.V, l ≫ A.v = z := by
  have hr : Set.range (z ≫ p) ⊆ Set.range A.u := by
    rintro _ ⟨t, rfl⟩
    rw [pt_eq]
    exact hz
  exact ⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm,
    A.pb.lift_fst _ _ _⟩

theorem UpperTheory.Gal.TranscendenceTraces.nwtGlue_of :
    NwtAgree → WtLocal → MultBC → GenBasic → NwtGlue := by
  intro hAg hLoc hBC hGen Z S p _ h
  choose A w hopen hmem hw using h
  have hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z := by
    intro Ω _ z
    haveI := hopen (pt (z ≫ p))
    exact lift_ex _ z (hmem _)
  choose l hlv using hl
  let W : Wt Z := fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)
  have hcomap : ∀ t, W.comap (A t).v = w t := by
    intro t
    funext Ω _ _ z
    haveI := hopen t
    haveI := hopen (pt ((z ≫ (A t).v) ≫ p))
    exact hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)
  refine ⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩
  · rw [hcomap s]
    exact (hw s).1
  · intro Ω _ _ z hz
    set s := pt (z ≫ p) with hs
    haveI := hopen s
    have hz' : GenPt (pt (l Ω z ≫ (A s).r)) := by
      rw [← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]
      exact hz
    have h1 := (hw s).2 Ω (l Ω z) hz'
    have h2 := hBC (A s).v (A s).r p (A s).u (A s).pb
    change w s Ω (l Ω z) = _
    rw [h1, h2]
    change mult p Ω (l Ω z ≫ (A s).v) = _
    rw [hlv Ω z]
