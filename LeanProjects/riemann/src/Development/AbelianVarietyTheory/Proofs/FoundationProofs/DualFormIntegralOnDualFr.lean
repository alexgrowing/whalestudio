import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem star_mem_one_of_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  have ha : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.isIntegral_coe
  have hb : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    ha.map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.mpr ⟨⟨_, hb⟩, rfl⟩

theorem inv_mulVec_star_mem_hdualFr {K : Type} [Field K] [NumberField K] [StarRing K] {N : ℕ}
    {H : Matrix (Fin N) (Fin N) K} (hd : IsUnit H.det) {M : Submodule (𝓞 K) (Fin N → K)} {x : Fin N → K}
    (hx : x ∈ dualFr M) : H⁻¹ *ᵥ star x ∈ hdualFr H M := by
  intro m hm
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  have h := star_mem_one_of_mem_one (hx m hm)
  rw [← Matrix.star_dotProduct_star] at h
  exact h

theorem dualForm_integral_on_dualFr : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (N : ℕ) (H : Matrix (Fin N) (Fin N) K), Hᴴ = H → IsUnit H.det → ∀ (M : Submodule (𝓞 K) (Fin N → K)) (s : ℕ), (∀ x ∈ hdualFr H M, ∀ y ∈ hdualFr H M, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → ∀ x ∈ dualFr M, ∀ y ∈ dualFr M, (s : K) * (star x ⬝ᵥ (H⁻¹)ᵀ *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ _ N H hH hd M s h x hx y hy
  have key := h _ (inv_mulVec_star_mem_hdualFr hd hy) _ (inv_mulVec_star_mem_hdualFr hd hx)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec, Matrix.star_mulVec, star_star,
    Matrix.conjTranspose_nonsing_inv, hH, ← Matrix.mulVec_transpose, dotProduct_comm] at key
  exact key

end GlobalTheory.TestLat
