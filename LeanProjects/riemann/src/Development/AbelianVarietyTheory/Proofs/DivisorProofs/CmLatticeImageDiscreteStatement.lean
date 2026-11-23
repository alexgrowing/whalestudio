import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeImageDiscrete
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_image_discrete : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (L : Submodule (OF E) E), (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    ∀ (Λ : Submodule ℤ (Fin n → ℂ)), (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ φ (e j) x) → DiscreteTopology Λ := by
  first | exact @GlobalTheory.CMLatticeDiscrete.cmLattice_discrete | exact GlobalTheory.CMLatticeDiscrete.cmLattice_discrete | (intros; apply GlobalTheory.CMLatticeDiscrete.cmLattice_discrete <;> assumption)
