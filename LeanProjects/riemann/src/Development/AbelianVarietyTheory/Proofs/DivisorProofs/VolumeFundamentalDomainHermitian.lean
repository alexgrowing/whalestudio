import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis

open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem volume_fundamentalDomain_eq_inv_det_of_unimodular :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Hm : Matrix (Fin g) (Fin g) ℂ)
      (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ)),
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.PosDef →
      (∀ a b : Λ, (Ef a b : ℝ) = ((a : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (b : Fin g → ℂ))).im) →
      Function.Bijective Ef → IsAddFundamentalDomain Λ Fd volume →
      volume Fd = ENNReal.ofReal (1 / Hm.det.re) := by
  intro g Λ _ Hm Ef Fd hspan hP hE hbij hFd
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 →
      0 < (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re := by
    intro z hz
    have h := hP.dotProduct_mulVec_pos (x := star z) (by simpa using hz)
    rw [star_star] at h
    exact (Complex.pos_iff.1 h).1
  have h := volume_mul_det_eq_one_of_unimodular g Λ hspan Hm Ef Fd hP.isHermitian hpos hE hbij hFd
  have hne : volume Fd ≠ ⊤ := by
    intro ht
    rw [ht] at h
    simp at h
  have hd : Hm.det.re ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  rw [← ENNReal.ofReal_toReal hne, eq_div_of_mul_eq hd h]
