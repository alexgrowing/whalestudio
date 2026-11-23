import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWChain

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (X := (op (SimplexCategory.mk n), op (SimplexCategory.mk m)))
    (Y := (op (SimplexCategory.mk p), op (SimplexCategory.mk q)))
    (Z := (op (SimplexCategory.mk r), op (SimplexCategory.mk s))) (α.op, β.op) (α'.op, β'.op) 1 1
  simp only [mul_one] at this
  exact this

theorem comp_apply' {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (j : Fin (a+1)) :
    ((f ≫ g).toOrderHom j : ℕ) = (g.toOrderHom (f.toOrderHom j) : ℕ) := rfl

theorem hom_ext' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ j : Fin (a+1), (f.toOrderHom j : ℕ) = (g.toOrderHom j : ℕ)) : f = g := by
  apply SimplexCategory.Hom.ext
  ext j
  exact h j

theorem faceFun_lt {i j : ℕ} (h : j < i) : faceFun i j = j := if_pos h
theorem faceFun_ge {i j : ℕ} (h : i ≤ j) : faceFun i j = j + 1 := if_neg (by omega)

theorem backc_apply (n a b : ℕ) (j : Fin (b+1)) : ((backc n a b).toOrderHom j : ℕ) = min n (a + j) := rfl
theorem idc_apply (n m : ℕ) (j : Fin (m+1)) : ((idc n m).toOrderHom j : ℕ) = min n j := rfl
theorem fc_apply (n m i : ℕ) (j : Fin (m+1)) : ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

section
variable (a b : ℕ)

theorem front_face_low (i : ℕ) (hi : i ≤ a) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = fc (a+1) a i ≫ idc (a+b+1) (a+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (j:ℕ) i with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem back_face_low (i : ℕ) (hi : i ≤ a) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) i = idc b b ≫ backc (a+b+1) (a+1) b := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

theorem front_face_high (i : ℕ) (hi : a < i) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_high (j : ℕ) (hj : j ≤ b) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) (a+1+j) = fc (b+1) b (j+1) ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro k; have hk := k.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (k:ℕ) (j+1) with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem front_face_cancel : fc (a+1) a (a+1) ≫ idc (a+b+1) (a+1) = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_cancel : idc b b ≫ backc (a+b+1) (a+1) b = fc (b+1) b 0 ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

end

theorem dT_h (a b : ℕ) : dT (a+1) b a b = ∑ i ∈ Finset.range (a+1+1), ((-1 : ℤ) ^ i) • bop (fc (a+1) a i) (idc b b) := by
  simp [dT, dH, dV]

theorem dT_v (a b : ℕ) : dT a (b+1) a b = ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b+1+1), ((-1 : ℤ) ^ j) • bop (idc a a) (fc (b+1) b j) := by
  simp [dT, dH, dV]

theorem dT_zero (x y a b : ℕ) (h1 : ¬ (x = a + 1 ∧ y = b)) (h2 : ¬ (x = a ∧ y = b + 1)) : dT x y a b = 0 := by
  simp [dT, dH, dV, h1, h2]

end GlobalTheory.EZ.AWChain

namespace GlobalTheory.EZ
open GlobalTheory.EZ.AWChain

theorem awO_comm_d : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  intro n a b hab
  subst hab
  rw [Finset.sum_eq_add (a + 1, b) (a, b + 1) (by simp)]
  rotate_left
  · rintro c hc ⟨h1, h2⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  simp only [dT_h, dT_v]
  have e1 : awO (a + b + 1) (a + 1) b = bop (idc (a+b+1) (a+1)) (backc (a+b+1) (a+1) b) := if_pos (by omega)
  have e2 : awO (a + b + 1) a (b + 1) = bop (idc (a+b+1) a) (backc (a+b+1) a (b+1)) := if_pos (by omega)
  have e3 : awO (a + b) a b = bop (idc (a+b) a) (backc (a+b) a b) := if_pos rfl
  have e4 : dD (a + b + 1) (a + b) = ∑ i ∈ Finset.range (a+b+1+1),
      ((-1 : ℤ) ^ i) • bop (fc (a+b+1) (a+b) i) (fc (a+b+1) (a+b) i) := if_pos rfl
  rw [e1, e2, e3, e4]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    bop_comp]
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Finset.sum_range_add]
  conv_rhs => rw [Finset.sum_range_succ _ (a + 1), Finset.sum_range_succ' _ (b + 1), smul_add]
  have hA : ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) i) (backc (a+b) a b ≫ fc (a+b+1) (a+b) i) =
      ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (fc (a+1) a i ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [front_face_low a b i (by omega), back_face_low a b i (by omega)]
  have hB : ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (a + 1 + j)) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) (a + 1 + j)) (backc (a+b) a b ≫ fc (a+b+1) (a+b) (a + 1 + j)) =
      ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (j + 1)) •
      bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b (j + 1) ≫ backc (a+b+1) a (b+1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [front_face_high a b (a + 1 + j) (by omega), back_face_high a b j (by omega), smul_smul, ← pow_add, show a + (j + 1) = a + 1 + j by omega]
  have hC : ((-1 : ℤ) ^ (a + 1)) • bop (fc (a+1) a (a + 1) ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b)
      + ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ 0) • bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b 0 ≫ backc (a+b+1) a (b+1))) = 0 := by
    rw [front_face_cancel, back_face_cancel, smul_smul, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [hA, hB, add_add_add_comm, hC, add_zero]

end GlobalTheory.EZ

example : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := GlobalTheory.EZ.awO_comm_d
