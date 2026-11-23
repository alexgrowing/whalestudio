import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.WeightLie

open ReciprocityTheory.ChartRestriction.G GlobalTheory.FrameNormLie

theorem norm_diag_eq_norm_diag {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {A B : Matrix n n ℂ} (hA : Supp t w A) (hB : Supp t w B)
    (hB0 : ∀ j, B j j ≠ 0) (d : n → ℂ) (hd : ∀ j, d j ≠ 0)
    (h : Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ)) = Bᵀ * (Matrix.diagonal d * B.map (starRingEnd ℂ)))
    (a : n) : ‖A a a‖ = ‖B a a‖ := by
  have hu : IsUnit B.det := by
    rw [PerBor.det_of_support t w hinj B hB, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hB0 j
  have hi : Supp t w B⁻¹ := PerBor.inv_support t w B hu hB
  have h1 := norm_diag_eq_one hinj (hA.mul hi) d hd (by
    have e : B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]; simp
    have e' : B⁻¹ᵀ * Bᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    calc _ = B⁻¹ᵀ * (Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ))) * B⁻¹.map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᵀ * Bᵀ) * Matrix.diagonal d * (B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ)) := by
          rw [h]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [e, e', Matrix.one_mul, Matrix.mul_one]) a
  rw [Supp.mul_diag hinj hA hi, PerBor.inv_diag t w hinj B hu hB, norm_mul, norm_inv] at h1
  exact (mul_inv_eq_one₀ (norm_ne_zero_iff.2 (hB0 a))).1 h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem moveMat_diag_ne {Ψ : Finset (E →+* ℂ)} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r) {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (j : Fin g) : PerBor.moveMat q idx b j j ≠ 0 := by
  rw [PerBor.moveMat_diag _ idx hb]
  split_ifs
  · exact PerMove.bor_diag_ne hb _ _
  · exact inv_ne_zero (PerMove.bor_diag_ne hb _ _)

theorem exists_tri_pair {α : Type} [Fintype α] (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {t : Fin g → α}
    {w : Fin g → ℕ} (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (hs : ∀ b ∈ Bor X.Ψ r, Supp t w (PerBor.moveMat X.p0 idx b)) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ T T' : Matrix (Fin g) (Fin g) ℂ, Supp t w T ∧ Supp t w T' ∧ (∀ j, T j j ≠ 0) ∧
      (∀ j, T' j j = T j j * (PerBor.moveMat X.p0 idx b j j)⁻¹) ∧
      (∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T *ᵥ perVec X idx x v) (T *ᵥ perVec X idx x v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ)) ∧
      ∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T' *ᵥ perVec X idx (rmul (lact γ x) b) v)
        (T' *ᵥ perVec X idx (rmul (lact γ x) b) v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ) := by
  obtain ⟨x₀, b₀, hb₀, hgr, rfl⟩ :=
    (UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  have hd : IsUnit (PerBor.moveMat X.p0 idx b).det := by
    rw [PerBor.det_of_support t w hinj _ (hs b hb), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => moveMat_diag_ne _ idx hb j
  have hm : ∀ b ∈ Bor X.Ψ r, ∀ y v, PerBor.moveMat X.p0 idx b *ᵥ perVec X idx y v = perVec X idx (rmul y b) v :=
    fun b hb y v => (PerBor.moveMat_mulVec X.p0 idx hb X.Gm y v (perVec X idx y v) (perVec X idx (rmul y b) v)
      (fun _ => rfl) (fun _ => rfl)).symm
  have hi : Supp t w (PerBor.moveMat X.p0 idx b)⁻¹ := PerBor.inv_support t w _ hd (hs b hb)
  have he : rmul (lact γ x) b₀ = lact γ (rmul x b₀) := funext fun τ =>
    Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b₀ τ)
  have h2 : ∀ v, (PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹) *ᵥ
      perVec X idx (rmul (lact γ x) b) v = perVec X idx (lact γ (rmul x b₀)) v := fun v => by
    rw [← hm b hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, hm b₀ hb₀, he]
  refine ⟨PerBor.moveMat X.p0 idx b₀, PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹, hs b₀ hb₀,
    (hs b₀ hb₀).mul hi, moveMat_diag_ne _ idx hb₀, fun j => ?_, fun v v' => ?_, fun v v' => ?_⟩
  · rw [Supp.mul_diag hinj (hs b₀ hb₀) hi, PerBor.inv_diag t w hinj _ hd (hs b hb)]
  · rw [hm b₀ hb₀, hm b₀ hb₀, im_diag_ortho X idx _ hgr]
  · rw [h2, h2, im_diag_ortho X idx _ fun τ => (AR.Up.PairUnfoldPf.gram_lact X hγ _ τ).trans (hgr τ)]

end GlobalTheory.WeightLie
