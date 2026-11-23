import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeValNN

theorem typePrime_valuationSum_eq_logGap_all (D : D7) (X : ErrX D) : Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond D X := by
  intro i u j _ S hS
  have h1 : ∀ w ∈ S, SizeData₂.sz w (vNN X i u j w) =
      ∑ τ : D.what₂.Tau, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) := by
    intro w _
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    unfold SizeData₂.sz vNN
    rw [mul_div_cancel₀ _ he, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, GlobalTheory.TypeLoss.sum_half D _ (D.host.g_prime i) S hS _ (GlobalTheory.TypeLoss.tauPib_norm X i τ)]

theorem typePrime_valuationSum_eq_logGap_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX :=
  fun Fm x hx i => typePrime_valuationSum_eq_logGap_all (Fm.D x i) (Fm.ex x hx i).errX

end GlobalTheory.TypeValNN
