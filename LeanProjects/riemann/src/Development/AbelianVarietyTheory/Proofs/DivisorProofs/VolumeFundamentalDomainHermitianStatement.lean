import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeFundamentalDomainHermitian
import Mathlib
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_fundamental_domain_hermitian : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ)), Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.PosDef → (∀ a b : Λ, (Ef a b : ℝ) = ((a : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (b : Fin g → ℂ))).im) → Function.Bijective Ef → IsAddFundamentalDomain Λ Fd volume → volume Fd = ENNReal.ofReal (1 / Hm.det.re) := by
  first | exact @GlobalTheory.volume_fundamentalDomain_eq_inv_det_of_unimodular | exact GlobalTheory.volume_fundamentalDomain_eq_inv_det_of_unimodular | (intros; apply GlobalTheory.volume_fundamentalDomain_eq_inv_det_of_unimodular <;> assumption)
