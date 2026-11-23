import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tform_star_mul_self_eq_sum_cmp {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ}
    (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x : W ⊗[ℂ] (Fin d → ℂ)) :
    tform H (star B * B) x x = ∑ k, H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x) := by
  rw [tform_apply]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    Matrix.mul_apply, Matrix.star_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum,
    RingHom.id_apply]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

open scoped ComplexOrder MatrixOrder in
theorem UpperTheory.V.Lit.Bor.tformPos :
    UpperTheory.V.Lit.Bor.TformPos := by
  intro W _ _ d H N G hH hG
  classical
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef
  obtain ⟨B, hBs, -, hBB⟩ := sub_zero G ▸
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h0.isSelfAdjoint
      (QuasispectrumRestricts.nnreal_of_nonneg h0)
  have hB : G = star B * B := by rw [hBs.star_eq, hBB, sub_zero]
  have hself : ∀ y : W, H y y = ((H y y).re : ℂ) := by
    intro y
    have hc := hH.herm y y
    apply Complex.ext
    · simp
    · have := congrArg Complex.im hc
      simp at this
      simp
      linarith
  have hz : ∀ x ∈ tens d N, ∀ k : Fin d, (∑ i, B k i • Bor.cmp i x) ∈ N := by
    intro x hx k
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_tens.mp hx i)
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    rw [tform_apply, tform_apply, map_sum]
    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.herm, ← hG.isHermitian.apply j i]
    simp [mul_comm]
  · intro x hx
    rw [hB, tform_star_mul_self_eq_sum_cmp, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => hH.nonneg _ (hz x hx k)
  · intro x hx h
    rw [hB, tform_star_mul_self_eq_sum_cmp] at h
    have hre : ∑ k, (H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x)).re = 0 := by
      rw [← Complex.re_sum, h, Complex.zero_re]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hH.nonneg _ (hz x hx k))] at hre
    have hzero : ∀ k, (∑ i, B k i • Bor.cmp i x) = 0 := by
      intro k
      apply hH.definite _ (hz x hx k)
      rw [hself, hre k (Finset.mem_univ _), Complex.ofReal_zero]
    have hdet : IsUnit B.det := by
      have := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
      rw [hB, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right this
    have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
    have hcomp : ∀ l, Bor.cmp l x = 0 := by
      intro l
      have e : Bor.cmp l x = ∑ k, B⁻¹ l k • ∑ i, B k i • Bor.cmp i x := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul]
        have : ∀ i, ∑ k, B⁻¹ l k * B k i = (1 : Matrix (Fin d) (Fin d) ℂ) l i := by
          intro i
          rw [← hinv, Matrix.mul_apply]
        simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [e]
      simp [hzero]
    rw [← sum_cmp x]
    simp [hcomp]
