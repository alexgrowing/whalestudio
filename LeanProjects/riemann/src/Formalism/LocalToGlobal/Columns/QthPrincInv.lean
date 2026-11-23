import Formalism.LocalToGlobal.Columns.QthCloseScl

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n c : ℕ}

theorem qth_ext_close (g : Sp E n ≃ₗ[E] Sp E n) (N : ℕ) (hg : lqPrinc P N g) (i l : Fin (n + c)) :
    P.valuation E ((((toGLm E (n + c) (twZrExt (c := c) g) : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) - 1) i l) ≤
      WithZero.exp (-(N : ℤ)) := by
  have hcoe : ∀ W : Sp E (n + c) ≃ₗ[E] Sp E (n + c),
      ((toGLm E (n + c) W : GL (Fin (n + c)) E) : Matrix (Fin (n + c)) (Fin (n + c)) E) =
        LinearMap.toMatrix' (W : Sp E (n + c) →ₗ[E] Sp E (n + c)) := by
    intro W
    simp only [toGLm, Matrix.GeneralLinearGroup.toLin, LinearMap.GeneralLinearGroup.generalLinearEquiv,
      MulEquiv.trans_apply, MulEquiv.symm_symm, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
      Units.coe_map, MonoidHom.coe_coe]
    rfl
  set u : Fin (n + c) → E := Pi.single l 1 with hu0
  have hpi : ∀ y : Fin n → E, (Loc.inX E n c y) i = if h : (i : ℕ) < n then y ⟨i, h⟩ else 0 := by
    intro y
    simp only [Loc.inX, LinearMap.pi_apply]
    split_ifs <;> rfl
  have hval : ((twZrExt (c := c) g) u) i =
      Loc.inX E n c (g (LinearMap.funLeft E E (Fin.castAdd c) u)) i +
        (u i - Loc.inX E n c (LinearMap.funLeft E E (Fin.castAdd c) u) i) := by
    rw [twZrExt_apply]
    rfl
  rw [hcoe, Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, ← hu0, hval, hpi, hpi]
  by_cases hi : (i : ℕ) < n
  · rw [dif_pos hi, dif_pos hi]
    have hu : (LinearMap.funLeft E E (Fin.castAdd c)) u ⟨i, hi⟩ = u i := rfl
    rw [hu, sub_self, add_zero]
    by_cases hl : (l : ℕ) < n
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = Pi.single (⟨l, hl⟩ : Fin n) 1 := by
        ext j
        simp [hu0, LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
      rw [hu']
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l =
          (1 : Matrix (Fin n) (Fin n) E) ⟨i, hi⟩ ⟨l, hl⟩ := by
        simp [Matrix.one_apply, Fin.ext_iff]
      rw [h1]
      have h2 := hg ⟨i, hi⟩ ⟨l, hl⟩
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe] at h2
      exact h2
    · have hu' : LinearMap.funLeft E E (Fin.castAdd c) u = 0 := by
        ext j
        simp only [hu0, LinearMap.funLeft_apply, Pi.single_apply, Pi.zero_apply, Function.comp_apply]
        rw [if_neg]
        intro h
        apply hl
        rw [← h]
        exact j.isLt
      have h1 : (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
        rw [Matrix.one_apply_ne]
        intro h
        apply hl
        rw [← h]
        exact hi
      rw [hu', map_zero, Pi.zero_apply, h1, sub_zero, map_zero]
      exact zero_le'
  · rw [dif_neg hi, dif_neg hi, zero_add, sub_zero]
    have h3 : u i - (1 : Matrix (Fin (n + c)) (Fin (n + c)) E) i l = 0 := by
      simp [hu0, Pi.single_apply, Matrix.one_apply]
    rw [h3, map_zero]
    exact zero_le'

theorem qth_princ_inv {N : ℕ} (g : ↥(GLint E n P)) (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
    lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  unfold lqPrinc at hg ⊢
  intro i j
  set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
  set B := LinearMap.toMatrix'
    ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← LinearMap.toMatrix'_comp]
    have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
        ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
        rw [inv_mul_cancel]
        rfl
      exact hx
    rw [hc, LinearMap.toMatrix'_id]
  have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
    intro a k
    rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
      show _ ∈ localization₂ P.asIdeal (stdLat E n)
      rw [mem_localization_standardLattice]
      intro t
      rw [qth_intAt_iff]
      by_cases h : t = k
      · subst h
        simp
      · simp [Pi.single_apply, h]
    have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
      (g⁻¹ : GLint E n P).2
    have h2 := ((ChainCounts.mem_stabL_iff.1 hmem) _).2 hs
    have h3 := (mem_localization_standardLattice P _).1 h2 a
    rw [qth_intAt_iff] at h3
    exact h3
  have hBm : B - 1 = -(B * (A - 1)) := by
    rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
  rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ (fun k _ => ?_)
  rw [map_mul]
  calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
    _ ≤ _ := by rw [one_mul]; exact hg k j

end Ext

end Formalism.L2.Col
