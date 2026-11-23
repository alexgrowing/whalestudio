import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_transform {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (A B C D : ℤ) (hdet : A * D - B * C = 1)
    (hA : (A : ZMod N) = 1) (hD : (D : ZMod N) = 1) (hCN : (C : ZMod N) = 0)
    (hCl : (C : ZMod l) = 0) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex ((A * z + B) / (C * z + D))) = (C * z + D) ^ k * f (ofComplex z) := by
  let g : SL(2, ℤ) := ⟨!![A, B; C, D], by simp [Matrix.det_fin_two_of]; linarith⟩
  have hg : g ∈ lev N l := by
    refine Subgroup.mem_inf.2 ⟨(Gamma1_mem N g).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩ <;> simpa [g]
  let w : ℍ := ⟨z, hz⟩
  have h1 := congrFun (hf g hg) w
  rw [SL_slash_apply] at h1
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = C * z + D := by
    have e1 : g 1 0 = C := rfl
    have e2 : g 1 1 = D := rfl
    have := (show denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (w : ℂ) = ((g 1 0 : ℤ) : ℂ) * z + (g 1 1 : ℤ) by
      simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, w])
    rw [this, e1, e2]
  have hsm : ((g • w : ℍ) : ℂ) = (A * z + B) / (C * z + D) := by
    rw [specialLinearGroup_apply]; simp [g, w]
  have hne : (C * z + D : ℂ) ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  rw [hden] at h1
  have hw : ofComplex z = w := ofComplex_apply_of_im_pos hz
  rw [← hsm, ofComplex_apply, hw, ← h1, zpow_neg]
  field_simp

theorem lev_periodic {N l : ℕ} {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ γ ∈ lev N l, f ∣[k] γ = f) (z : ℂ) (hz : 0 < z.im) :
    f (ofComplex (z + 1)) = f (ofComplex z) := by
  have h := lev_transform hf 1 1 0 1 (by norm_num) (by simp) (by simp) (by simp) (by simp) z hz
  simpa using h

theorem sum_range_affine {q : ℕ} (hq : 0 < q) (F : ℤ → ℂ) (hF : Function.Periodic F q)
    (u v : ℤ) (hu : ∃ w : ZMod q, w * u = 1) :
    ∑ j ∈ Finset.range q, F (v + u * j) = ∑ j ∈ Finset.range q, F j := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let G : ZMod q → ℂ := fun x => F (x.val : ℤ)
  have hFG : ∀ m : ℤ, F m = G m := by
    intro m
    simp only [G, ZMod.val_intCast]
    have := (hF.int_mul (m / q)) (m % q)
    rw [← this]; congr 1
    rw [Int.cast_id]; linear_combination (Int.mul_ediv_add_emod m q).symm
  have hsum : ∀ H : ZMod q → ℂ, ∑ j ∈ Finset.range q, H (j : ZMod q) = ∑ x, H x := by
    intro H
    symm
    refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j _; exact Finset.mem_univ _
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _; rw [ZMod.natCast_zmod_val]
  obtain ⟨w, hw⟩ := hu
  have hbij : Function.Bijective (fun x : ZMod q => (v : ZMod q) + u * x) := by
    refine Finite.injective_iff_bijective.1 ?_
    intro x y hxy
    have : (u : ZMod q) * x = u * y := add_left_cancel hxy
    calc x = w * (u * x) := by rw [← mul_assoc, hw, one_mul]
      _ = y := by rw [this, ← mul_assoc, hw, one_mul]
  calc ∑ j ∈ Finset.range q, F (v + u * j)
      = ∑ j ∈ Finset.range q, G ((v : ZMod q) + u * (j : ZMod q)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl
    _ = ∑ x, G ((v : ZMod q) + u * x) := hsum (fun x => G ((v : ZMod q) + u * x))
    _ = ∑ x, G x := hbij.sum_comp G
    _ = ∑ j ∈ Finset.range q, G (j : ZMod q) := (hsum G).symm
    _ = ∑ j ∈ Finset.range q, F j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hFG]; push_cast; rfl

theorem uOp_slash_lev : ∀ (N l q : ℕ) (k : ℤ) (f : ℍ → ℂ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    (∀ γ ∈ lev N l, f ∣[k] γ = f) → ∀ γ ∈ lev N l, uOp q f ∣[k] γ = uOp q f := by
  intro N l q k f _ _ hq hqNl hf γ hγ
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hγ
  rw [Gamma1_mem] at h1
  rw [Gamma0_mem] at h0
  obtain ⟨ha, hd, hcN⟩ := h1
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hqc : (q : ℤ) ∣ γ 1 0 := by
    rcases hq.dvd_mul.1 hqNl with h | h
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 hcN)
    · exact (Int.natCast_dvd_natCast.2 h).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 h0)
  obtain ⟨t, ht⟩ := hqc
  funext τ
  rw [SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (τ : ℂ) = (γ 1 0 : ℂ) * τ + γ 1 1 := by
    simp [denom, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hsm : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + γ 0 1) / ((γ 1 0 : ℂ) * τ + γ 1 1) := by
    rw [specialLinearGroup_apply]; simp
  have hcd : (γ 1 0 : ℂ) * τ + γ 1 1 ≠ 0 := by rw [← hden]; exact denom_ne_zero _ _
  set a := γ 0 0 with ha_def
  set b := γ 0 1 with hb_def
  set c := γ 1 0 with hc_def
  set d := γ 1 1 with hd_def
  let F : ℤ → ℂ := fun m => f (ofComplex (((τ : ℂ) + m) / q))
  have hzim : ∀ m : ℤ, 0 < (((τ : ℂ) + m) / q).im := by
    intro m
    have : (((τ : ℂ) + m) / q).im = τ.im / q := by simp [Complex.div_natCast_im]
    rw [this]; exact div_pos τ.im_pos hqpos
  have hper : Function.Periodic F (q : ℤ) := by
    intro m
    have e : ((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q = ((τ : ℂ) + m) / q + 1 := by
      push_cast; field_simp; ring
    show f (ofComplex (((τ : ℂ) + ((m + q : ℤ) : ℂ)) / q)) = f (ofComplex (((τ : ℂ) + m) / q))
    rw [e]; exact lev_periodic hf _ (hzim m)
  have hterm : ∀ j : ℕ, f (ofComplex (((a * τ + b) / (c * τ + d) + j) / q)) =
      (c * τ + d) ^ k * F (d * b + d * d * j) := by
    intro j
    set j' : ℤ := d * b + d * d * j with hj'
    set e : ℤ := t * (-(b * b) - 2 * j * b * d - j * j * d * d) with he_def
    have he : e * q = b + j * d - (a + j * c) * j' := by
      rw [he_def, hj']
      linear_combination (b + j * d) * hdet + (b * b + 2 * j * b * d + j * j * d * d) * ht
    have heC : (e : ℂ) * q = b + j * d - (a + j * c) * j' := by exact_mod_cast he
    have h := lev_transform hf (a + j * c) e (q * c) (d - c * j')
      (by linear_combination hdet - c * he)
      (by push_cast; simp [ha, hcN]) (by push_cast; simp [hd, hcN]) (by push_cast; simp [hcN])
      (by push_cast; simp [h0]) _ (hzim j')
    have hCD : ((q * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + ((d - c * j' : ℤ) : ℂ) = c * τ + d := by
      push_cast; field_simp; ring
    rw [hCD] at h
    have harg : (((a + j * c : ℤ) : ℂ) * (((τ : ℂ) + j') / q) + (e : ℂ)) / (c * τ + d) =
        ((a * τ + b) / (c * τ + d) + j) / q := by
      push_cast
      field_simp
      linear_combination heC
    rw [harg] at h
    exact h
  have hunit : ∃ w : ZMod q, w * ((d * d : ℤ) : ZMod q) = 1 := by
    refine ⟨(a : ZMod q) * a, ?_⟩
    have h := congrArg (Int.cast : ℤ → ZMod q) hdet
    rw [ht] at h
    push_cast at h
    rw [ZMod.natCast_self] at h
    push_cast
    linear_combination ((a : ZMod q) * d + 1) * h
  unfold uOp
  rw [hsm, hden]
  simp_rw [hterm]
  rw [← Finset.mul_sum, sum_range_affine hq.pos F hper _ _ hunit]
  have hF : ∑ j ∈ Finset.range q, F j =
      ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q)) := by simp [F]
  rw [hF, zpow_neg]
  field_simp

end GlobalTheory.Hk
