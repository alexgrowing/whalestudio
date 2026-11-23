import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by
        rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
