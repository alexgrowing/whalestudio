import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaceSubMid

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.AWChain

open GlobalTheory.EtC.CupSpec (sub_δ_val δ_sub_val sub_val hom_ext_val)

def cm (N j l : ℕ) : SimplexCategory.mk l ⟶ SimplexCategory.mk N :=
  if h : j + l ≤ N then SimplexCategory.subinterval j l h else SimplexCategory.const _ _ 0

theorem cm_eq (N j l : ℕ) (h : j + l ≤ N) : cm N j l = SimplexCategory.subinterval j l h := dif_pos h

section
variable {N : ℕ}

theorem cm_δ_le (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : (i : ℕ) ≤ j) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) (j + 1) l := by
  rw [cm_eq N j l h, cm_eq (N + 1) (j + 1) l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_gt (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (hi : j + l < (i : ℕ)) : cm N j l ≫ SimplexCategory.δ i = cm (N + 1) j l := by
  rw [cm_eq N j l h, cm_eq (N + 1) j l (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, sub_val]
  split_ifs <;> omega

theorem cm_δ_mid (j l : ℕ) (h : j + l ≤ N) (i : Fin (N + 2)) (i' : Fin (l + 2)) (hi : (i : ℕ) = j + i') :
    cm N j l ≫ SimplexCategory.δ i = SimplexCategory.δ i' ≫ cm (N + 1) j (l + 1) := by
  rw [cm_eq N j l h, cm_eq (N + 1) j (l + 1) (by omega)]
  refine hom_ext_val _ _ fun v => ?_
  rw [sub_δ_val, δ_sub_val]
  split_ifs <;> omega

end

theorem telescope {N : ℕ} {A : Type*} [AddCommGroup A] {p r : ℕ} (hN : p + r = N)
    (φ : (SimplexCategory.mk p ⟶ SimplexCategory.mk (N + 1)) → (SimplexCategory.mk r ⟶ SimplexCategory.mk (N + 1)) → A) :
    ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • φ (cm N 0 p ≫ SimplexCategory.δ i) (cm N p r ≫ SimplexCategory.δ i) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • φ (SimplexCategory.δ i ≫ cm (N + 1) 0 (p + 1)) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) •
        φ (cm (N + 1) 0 p) (SimplexCategory.δ j ≫ cm (N + 1) p (r + 1)) := by
  have e1 : SimplexCategory.δ (Fin.last (p + 1)) ≫ cm (N + 1) 0 (p + 1) = cm (N + 1) 0 p := by
    rw [cm_eq (N + 1) 0 (p + 1) (by omega), cm_eq (N + 1) 0 p (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    have := v.2
    simp only [Fin.val_last]
    split_ifs <;> omega
  have e2 : SimplexCategory.δ 0 ≫ cm (N + 1) p (r + 1) = cm (N + 1) (p + 1) r := by
    rw [cm_eq (N + 1) p (r + 1) (by omega), cm_eq (N + 1) (p + 1) r (by omega)]
    refine hom_ext_val _ _ fun v => ?_
    rw [δ_sub_val, sub_val]
    simp; omega
  rw [← Fin.sum_congr' _ (show (p + 1) + (r + 1) = N + 2 by omega), Fin.sum_univ_add,
    Fin.sum_univ_castSucc (n := p + 1), Fin.sum_univ_succ (n := r + 1), e1, e2, smul_add, Finset.smul_sum]
  have c : (-1 : ℤ) ^ ((Fin.last (p + 1) : Fin (p + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) +
      (-1 : ℤ) ^ p • (-1 : ℤ) ^ ((0 : Fin (r + 2)) : ℕ) • φ (cm (N + 1) 0 p) (cm (N + 1) (p + 1) r) = 0 := by
    simp [pow_succ]
  have key : ∀ a b c d e f : A, c + d = 0 → a = e → b = f → a + b = e + c + (d + f) := by
    rintro a b c d _ _ h rfl rfl
    rw [add_assoc, ← add_assoc c, h, zero_add]
  refine key _ _ _ _ _ _ c (Finset.sum_congr rfl fun i _ => ?_) (Finset.sum_congr rfl fun j _ => ?_)
  · have := i.2
    rw [cm_δ_mid 0 p (by omega) _ i.castSucc (by simp), cm_δ_le p r (by omega) _ (by simp; omega)]
    rfl
  · have := j.2
    rw [cm_δ_mid p r (by omega) _ j.succ (by simp; omega), cm_δ_gt 0 p (by omega) _ (by simp; omega), smul_smul, ← pow_add]
    congr 2
    simp; omega

theorem aw_eq (N : ℕ) : Pr.aw N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    Finsupp.single (⟨q.1, q.2, cm N 0 q.1, cm N q.1 q.2⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.aw]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega)]

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) (1 : ℤ) := by
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem d_aw (N : ℕ) : Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) := by
  rw [aw_eq, aw_eq, map_sum]
  simp only [Pr.d, Finsupp.linearCombination_single, one_smul, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ']
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]
  simp only [Pr.bd, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  symm
  refine (telescope hN (fun a b => Finsupp.single (⟨q.1, q.2, a, b⟩ : Pr (N + 1)) (1 : ℤ))).trans ?_
  rw [Finset.smul_sum]

theorem wa_eq (N : ℕ) : Pr.wa N = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal N,
    (-1 : ℤ) ^ (q.1 * q.2) • Finsupp.single (⟨q.2, q.1, cm N q.1 q.2, cm N 0 q.1⟩ : Pr N) (1 : ℤ) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range, Pr.wa]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  rw [cm_eq N 0 p (by omega), cm_eq N p (N - p) (by omega), Finsupp.smul_single, smul_eq_mul, mul_one]

theorem d_wa (N : ℕ) : Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) := by
  rw [wa_eq, wa_eq, map_sum]
  simp only [map_zsmul, Pr.d, Finsupp.linearCombination_single, one_smul, smul_add, Finset.sum_add_distrib]
  rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
  simp only [d₁_zero, d₂_zero, smul_zero, zero_add, d₁_succ, d₂_succ]
  simp only [Pr.bd, map_sum, map_zsmul, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hN : q.1 + q.2 = N := by simpa using hq
  obtain ⟨p, r⟩ := q
  dsimp only at hN ⊢
  have T := telescope hN (fun a b => Finsupp.single (⟨r, p, b, a⟩ : Pr (N + 1)) (1 : ℤ))
  conv_rhs => arg 2; ext x; rw [smul_comm]
  rw [← Finset.smul_sum (r := (-1 : ℤ) ^ (p * r)), T, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  conv_rhs => rw [add_comm]
  have s1 : (-1 : ℤ) ^ (p * (r + 1)) = (-1) ^ (p * r) * (-1) ^ p := by ring
  have s2 : (-1 : ℤ) ^ ((p + 1) * r) * (-1) ^ r = (-1) ^ (p * r) := by
    rw [← pow_add, show (p + 1) * r + r = p * r + 2 * r by ring, pow_add, pow_mul]
    norm_num
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_
  · simp only [smul_smul, s1, mul_assoc]
  · simp only [smul_smul]
    rw [← mul_assoc, s2]

theorem aw_wa_chain : ∀ N, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N) ∧
    Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N) :=
  fun N => ⟨d_aw N, d_wa N⟩

end GlobalTheory.EtC.AWChain

end
