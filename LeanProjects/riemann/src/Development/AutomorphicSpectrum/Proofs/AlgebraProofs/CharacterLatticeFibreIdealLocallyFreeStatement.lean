import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeFibreIdealLocallyFree
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_lattice_fibre_ideal_locally_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal.main <;> assumption)
