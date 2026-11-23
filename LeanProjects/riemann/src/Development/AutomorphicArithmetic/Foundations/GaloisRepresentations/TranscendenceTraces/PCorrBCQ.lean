import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem UpperTheory.Gal.TranscendenceTraces.corrBCQ_of :
    TrBCQ → CorrBCQ := by
  intro hT l _ n i S' Y' S Y c' c g g' v hpb hf hw hl
  haveI := c.fin
  haveI := c'.fin
  simp only [Corr.opQ]
  rw [← LinearMap.comp_assoc, hT l n i v c'.p c.p g c.w hpb c.wt hl, ← hw,
    LinearMap.comp_assoc, LinearMap.comp_assoc, ← pullHQ_comp', ← pullHQ_comp', hf]
