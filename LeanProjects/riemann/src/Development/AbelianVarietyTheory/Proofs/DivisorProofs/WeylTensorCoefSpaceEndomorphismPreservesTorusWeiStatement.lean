import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylTensorCoefSpaceEndomorphismPreservesTorusWei
import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylTensorCoefSpace_endomorphism_preserves_torus_weight : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : Module.End K (VV K lam)), (∀ (h : ι → GL (Fin n) K) v, g (rhoK lam h v) = rhoK lam h (g v)) → ∀ v : VV K lam, (∀ m ∈ (v : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a) → ∀ m ∈ ((g v : VV K lam) : Pol K ι n).support, ∀ τ a, ∑ s : Fin n, m (τ, a, s) = (lam τ).natW a := by
  first | exact @GlobalTheory.CoefTorusWeight.weight_preserved | exact GlobalTheory.CoefTorusWeight.weight_preserved | (intros; apply GlobalTheory.CoefTorusWeight.weight_preserved <;> assumption)
