import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.CosetReps

open Matrix

lemma lev_iff (N l : ℕ) (A : SL(2, ℤ)) : A ∈ Lev N l ↔
    ((mat A 0 0 : ℤ) : ZMod N) = 1 ∧ ((mat A 1 1 : ℤ) : ZMod N) = 1 ∧ ((mat A 1 0 : ℤ) : ZMod N) = 0 ∧
      ((mat A 1 0 : ℤ) : ZMod l) = 0 := by
  simp only [Lev, Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem, mat, and_assoc]

def slMk (a b c d : ℤ) (h : a * d - b * c = 1) : SL(2, ℤ) :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

@[simp] lemma mat_slMk (a b c d : ℤ) (h : a * d - b * c = 1) : mat (slMk a b c d h) = !![a, b; c, d] := rfl

lemma slMk_mem_lev {N l : ℕ} {a b c d : ℤ} (h : a * d - b * c = 1) (ha : (a : ZMod N) = 1)
    (hd : (d : ZMod N) = 1) (hc : (c : ZMod N) = 0) (hcl : (c : ZMod l) = 0) : slMk a b c d h ∈ Lev N l := by
  rw [lev_iff, mat_slMk]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa

private lemma sl2_entry_det_eq_one (g : SL(2, ℤ)) : mat g 0 0 * mat g 1 1 - mat g 0 1 * mat g 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  exact h

private lemma det_and_entries_mul_dg_mul_mod {N l : ℕ} (p : ℕ) (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1)
    (a1 : ((A 0 0 : ℤ) : ZMod N) = 1) (c1 : ((A 1 0 : ℤ) : ZMod N) = 0) (l1 : ((A 1 0 : ℤ) : ZMod l) = 0)
    (a2 : ((B 0 0 : ℤ) : ZMod N) = 1) (c2 : ((B 1 0 : ℤ) : ZMod N) = 0) (l2 : ((B 1 0 : ℤ) : ZMod l) = 0) :
    (A * dg 1 p * B) 0 0 * (A * dg 1 p * B) 1 1 - (A * dg 1 p * B) 0 1 * (A * dg 1 p * B) 1 0 = p ∧
    (((A * dg 1 p * B) 0 0 : ℤ) : ZMod N) = 1 ∧ (((A * dg 1 p * B) 1 0 : ℤ) : ZMod N) = 0 ∧
    (((A * dg 1 p * B) 1 0 : ℤ) : ZMod l) = 0 := by
  have h00 : (A * dg 1 p * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * p * B 1 0 := by
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : (A * dg 1 p * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * p * B 1 1 := by
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : (A * dg 1 p * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * p * B 1 0 := by
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : (A * dg 1 p * B) 1 1 = A 1 0 * B 0 1 + A 1 1 * p * B 1 1 := by
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination ((p : ℤ) * (B 0 0 * B 1 1 - B 0 1 * B 1 0)) * hA + (p : ℤ) * hB
  · push_cast
    linear_combination ((B 0 0 : ℤ) : ZMod N) * a1 + a2 + ((A 0 1 : ℤ) : ZMod N) * (p : ZMod N) * c2
  · push_cast
    linear_combination ((B 0 0 : ℤ) : ZMod N) * c1 + ((A 1 1 : ℤ) : ZMod N) * (p : ZMod N) * c2
  · push_cast
    linear_combination ((B 0 0 : ℤ) : ZMod l) * l1 + ((A 1 1 : ℤ) : ZMod l) * (p : ZMod l) * l2

lemma dc_entries {N l : ℕ} (p : ℕ) (γ₁ γ₂ : SL(2, ℤ)) (h₁ : γ₁ ∈ Lev N l) (h₂ : γ₂ ∈ Lev N l) :
    (mat γ₁ * dg 1 p * mat γ₂) 0 0 * (mat γ₁ * dg 1 p * mat γ₂) 1 1 -
      (mat γ₁ * dg 1 p * mat γ₂) 0 1 * (mat γ₁ * dg 1 p * mat γ₂) 1 0 = p ∧
    (((mat γ₁ * dg 1 p * mat γ₂) 0 0 : ℤ) : ZMod N) = 1 ∧
    (((mat γ₁ * dg 1 p * mat γ₂) 1 0 : ℤ) : ZMod N) = 0 ∧
    (((mat γ₁ * dg 1 p * mat γ₂) 1 0 : ℤ) : ZMod l) = 0 := by
  rw [lev_iff] at h₁ h₂
  exact det_and_entries_mul_dg_mul_mod p (mat γ₁) (mat γ₂) (sl2_entry_det_eq_one γ₁) (sl2_entry_det_eq_one γ₂) h₁.1 h₁.2.2.1 h₁.2.2.2 h₂.1 h₂.2.2.1 h₂.2.2.2

lemma exists_upper {N l p : ℕ} (hp : p.Prime) (hpN : IsUnit (p : ZMod N)) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = p) (ha : ((M 0 0 : ℤ) : ZMod N) = 1)
    (hc : ((M 1 0 : ℤ) : ZMod N) = 0) (hcl : ((M 1 0 : ℤ) : ZMod l) = 0)
    (hnd : ¬ (((M 0 0 : ℤ) : ZMod p) = 0 ∧ ((M 1 0 : ℤ) : ZMod p) = 0)) :
    ∃ j : ℕ, j < p ∧ ∃ γ : SL(2, ℤ), γ ∈ Lev N l ∧ M = mat γ * !![1, (j : ℤ); 0, (p : ℤ)] := by
  have := Fact.mk hp
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hdetp : ((M 0 0 : ℤ) : ZMod p) * ((M 1 1 : ℤ) : ZMod p) - ((M 0 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p) = 0 := by
    have e := congrArg (Int.cast : ℤ → ZMod p) hdet
    push_cast at e
    rw [e, ZMod.natCast_self]
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ZMod p, ((M 0 1 : ℤ) : ZMod p) = t * ((M 0 0 : ℤ) : ZMod p) ∧ ((M 1 1 : ℤ) : ZMod p) = t * ((M 1 0 : ℤ) : ZMod p) := by
    by_cases hx : ((M 0 0 : ℤ) : ZMod p) = 0
    · have hy : ((M 1 0 : ℤ) : ZMod p) ≠ 0 := fun hy => hnd ⟨hx, hy⟩
      have h1 : ((M 1 0 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hy
      refine ⟨((M 1 1 : ℤ) : ZMod p) * ((M 1 0 : ℤ) : ZMod p)⁻¹, ?_, ?_⟩
      · linear_combination -(((M 1 0 : ℤ) : ZMod p)⁻¹) * hdetp - ((M 0 1 : ℤ) : ZMod p) * h1
      · linear_combination -(((M 1 1 : ℤ) : ZMod p)) * h1
    · have h1 : ((M 0 0 : ℤ) : ZMod p) * ((M 0 0 : ℤ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hx
      refine ⟨((M 0 1 : ℤ) : ZMod p) * ((M 0 0 : ℤ) : ZMod p)⁻¹, ?_, ?_⟩
      · linear_combination -(((M 0 1 : ℤ) : ZMod p)) * h1
      · linear_combination ((M 0 0 : ℤ) : ZMod p)⁻¹ * hdetp - ((M 1 1 : ℤ) : ZMod p) * h1
  have hb : (p : ℤ) ∣ M 0 1 - M 0 0 * (t.val : ℤ) := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [ht1]; ring
  have hd : (p : ℤ) ∣ M 1 1 - M 1 0 * (t.val : ℤ) := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [ht2]; ring
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨d', hd'⟩ := hd
  have hdet' : M 0 0 * d' - b' * M 1 0 = 1 := by
    apply mul_left_cancel₀ hp0
    linear_combination -(M 0 0) * hd' + M 1 0 * hb' + hdet
  refine ⟨t.val, ZMod.val_lt t, slMk _ _ _ _ hdet', slMk_mem_lev hdet' ha ?_ hc hcl, ?_⟩
  · have e := congrArg (Int.cast : ℤ → ZMod N) hdet'
    push_cast at e
    linear_combination e - ((d' : ℤ) : ZMod N) * ha + ((b' : ℤ) : ZMod N) * hc
  · rw [mat_slMk]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, -ZMod.natCast_val] <;> first | linear_combination hb' | linear_combination hd'

lemma upper_mem (N l p j : ℕ) :
    ∃ γ₁ γ₂ : Lev N l, !![1, (j : ℤ); 0, (p : ℤ)] = mat γ₁ * dg 1 p * mat γ₂ := by
  have h : (1 : ℤ) * 1 - (j : ℤ) * 0 = 1 := by ring
  refine ⟨1, ⟨slMk 1 j 0 1 h, slMk_mem_lev h (by simp) (by simp) (by simp) (by simp)⟩, ?_⟩
  show !![1, (j : ℤ); 0, (p : ℤ)] = (1 : Matrix (Fin 2) (Fin 2) ℤ) * dg 1 p * mat (slMk 1 j 0 1 h)
  rw [Matrix.one_mul, mat_slMk]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

lemma upper_rel {p i j : ℕ} (hi : i < p) (hj : j < p) (k : Matrix (Fin 2) (Fin 2) ℤ)
    (h : !![1, (i : ℤ); 0, (p : ℤ)] = k * !![1, (j : ℤ); 0, (p : ℤ)]) : i = j := by
  have e00 : (1 : ℤ) = k 0 0 := by
    have e := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using e
  have e01 : (i : ℤ) = k 0 0 * j + k 0 1 * p := by
    have e := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using e
  have hi' : (i : ℤ) < p := by exact_mod_cast hi
  have hj' : (j : ℤ) < p := by exact_mod_cast hj
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hj0 : (0 : ℤ) ≤ j := by positivity
  rw [← e00, one_mul] at e01
  have hk : k 0 1 = 0 := by
    rcases lt_trichotomy (k 0 1) 0 with hneg | hz | hpos
    · nlinarith [mul_le_mul_of_nonneg_right (show k 0 1 ≤ -1 by omega) (show (0 : ℤ) ≤ p by positivity)]
    · exact hz
    · nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ k 0 1 by omega) (show (0 : ℤ) ≤ p by positivity)]
  rw [hk, zero_mul, add_zero] at e01
  exact_mod_cast e01

lemma not_upper_eq_diag {p i : ℕ} (hp : p.Prime) (k s : Matrix (Fin 2) (Fin 2) ℤ)
    (h : !![1, (i : ℤ); 0, (p : ℤ)] = k * (s * dg p 1)) : False := by
  have e := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, dg] at e
  have hd : (p : ℤ) ∣ 1 := ⟨k 0 0 * s 0 0 + k 0 1 * s 1 0, by linear_combination e⟩
  exact hp.not_dvd_one (by exact_mod_cast hd)

lemma cast_zero_of_mul {N l : ℕ} {x : ℤ} (h : (x : ZMod (N * l)) = 0) :
    (x : ZMod N) = 0 ∧ (x : ZMod l) = 0 := by
  rw [CharP.intCast_eq_zero_iff (ZMod (N * l)) (N * l)] at h
  push_cast at h
  exact ⟨(CharP.intCast_eq_zero_iff (ZMod N) N x).2 (dvd_trans (dvd_mul_right _ _) h),
    (CharP.intCast_eq_zero_iff (ZMod l) l x).2 (dvd_trans (dvd_mul_left _ _) h)⟩

lemma diam_facts {N l : ℕ} {d : ZMod N} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) :
    ((mat σ 1 0 : ℤ) : ZMod N) = 0 ∧ ((mat σ 1 0 : ℤ) : ZMod l) = 0 ∧ ((mat σ 1 1 : ℤ) : ZMod N) = d ∧
      ((mat σ 0 0 : ℤ) : ZMod N) * d = 1 := by
  obtain ⟨h0, h1⟩ := hσ
  rw [CongruenceSubgroup.Gamma0_mem] at h0
  obtain ⟨hN, hl⟩ := cast_zero_of_mul h0
  refine ⟨hN, hl, h1, ?_⟩
  have e := congrArg (Int.cast : ℤ → ZMod N) (sl2_entry_det_eq_one σ)
  push_cast at e
  linear_combination e - ((mat σ 0 0 : ℤ) : ZMod N) * h1 + ((mat σ 0 1 : ℤ) : ZMod N) * hN

lemma diam_case {N l q : ℕ} (hq0 : q ≠ 0) (hqN : IsUnit (q : ZMod N)) (hql : IsUnit (q : ZMod l))
    (σ : SL(2, ℤ)) (hσ : IsDiam N l (q : ZMod N) σ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = q) (ha : ((M 0 0 : ℤ) : ZMod N) = 1)
    (hc : ((M 1 0 : ℤ) : ZMod N) = 0) (hcl : ((M 1 0 : ℤ) : ZMod l) = 0)
    (hqa : (q : ℤ) ∣ M 0 0) (hqc : (q : ℤ) ∣ M 1 0) :
    ∃ γ : SL(2, ℤ), γ ∈ Lev N l ∧ M = mat γ * (mat σ * dg q 1) := by
  obtain ⟨a', ha'⟩ := hqa
  obtain ⟨c', hc'⟩ := hqc
  have hσd := sl2_entry_det_eq_one σ
  obtain ⟨hs10N, hs10l, hs11, -⟩ := diam_facts hσ
  have hq0' : (q : ℤ) ≠ 0 := by exact_mod_cast hq0
  have hK : a' * M 1 1 - M 0 1 * c' = 1 := by
    apply mul_left_cancel₀ hq0'
    linear_combination hdet - M 1 1 * ha' + M 0 1 * hc'
  have hg : (a' * mat σ 1 1 - M 0 1 * mat σ 1 0) * (-(c' * mat σ 0 1) + M 1 1 * mat σ 0 0) -
      (-(a' * mat σ 0 1) + M 0 1 * mat σ 0 0) * (c' * mat σ 1 1 - M 1 1 * mat σ 1 0) = 1 := by
    linear_combination (a' * M 1 1 - M 0 1 * c') * hσd + hK
  have ha'N := congrArg (Int.cast : ℤ → ZMod N) ha'
  have hc'N := congrArg (Int.cast : ℤ → ZMod N) hc'
  push_cast at ha'N hc'N
  have hc'l : ((c' : ℤ) : ZMod l) = 0 := by
    have e := congrArg (Int.cast : ℤ → ZMod l) hc'
    push_cast at e
    rw [e] at hcl
    exact hql.mul_right_eq_zero.1 hcl
  have hA : ((a' * mat σ 1 1 - M 0 1 * mat σ 1 0 : ℤ) : ZMod N) = 1 := by
    push_cast
    linear_combination ((a' : ℤ) : ZMod N) * hs11 - ((M 0 1 : ℤ) : ZMod N) * hs10N - ha'N + ha
  have hC : ((c' * mat σ 1 1 - M 1 1 * mat σ 1 0 : ℤ) : ZMod N) = 0 := by
    push_cast
    linear_combination ((c' : ℤ) : ZMod N) * hs11 - ((M 1 1 : ℤ) : ZMod N) * hs10N - hc'N + hc
  have hCl : ((c' * mat σ 1 1 - M 1 1 * mat σ 1 0 : ℤ) : ZMod l) = 0 := by
    push_cast
    linear_combination ((mat σ 1 1 : ℤ) : ZMod l) * hc'l - ((M 1 1 : ℤ) : ZMod l) * hs10l
  have hD : ((-(c' * mat σ 0 1) + M 1 1 * mat σ 0 0 : ℤ) : ZMod N) = 1 := by
    have e := congrArg (Int.cast : ℤ → ZMod N) hg
    have hA' := hA
    have hC' := hC
    push_cast at e hA' hC' ⊢
    linear_combination e - (-(((c' : ℤ) : ZMod N) * ((mat σ 0 1 : ℤ) : ZMod N)) + ((M 1 1 : ℤ) : ZMod N) * ((mat σ 0 0 : ℤ) : ZMod N)) * hA' +
      (-(((a' : ℤ) : ZMod N) * ((mat σ 0 1 : ℤ) : ZMod N)) + ((M 0 1 : ℤ) : ZMod N) * ((mat σ 0 0 : ℤ) : ZMod N)) * hC'
  refine ⟨slMk _ _ _ _ hg, slMk_mem_lev hg hA hD hC hCl, ?_⟩
  rw [mat_slMk]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ha' - (q : ℤ) * a' * hσd
  · linear_combination -(M 0 1) * hσd
  · linear_combination hc' - (q : ℤ) * c' * hσd
  · linear_combination -(M 1 1) * hσd

lemma mat_mul' (a b : SL(2, ℤ)) : mat (a * b) = mat a * mat b := rfl

lemma mat_one' : mat 1 = 1 := rfl

lemma cancel_left (g g' : SL(2, ℤ)) {X Y : Matrix (Fin 2) (Fin 2) ℤ} (h : mat g * X = mat g' * Y) :
    X = mat (g⁻¹ * g') * Y := by
  rw [mat_mul', Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mul]

lemma tqFam_lt {q : ℕ} (σ : SL(2, ℤ)) (i : Fin (q + 1)) (hi : (i : ℕ) < q) :
    tqFam q σ i = !![1, ((i : ℕ) : ℤ); 0, (q : ℤ)] := by simp [tqFam, hi]

lemma tqFam_ge {q : ℕ} (σ : SL(2, ℤ)) (i : Fin (q + 1)) (hi : ¬ (i : ℕ) < q) :
    tqFam q σ i = mat σ * dg q 1 := by simp [tqFam, hi]

lemma tq_inj {q : ℕ} (hq : q.Prime) (σ g g' : SL(2, ℤ)) (i i' : Fin (q + 1))
    (h : mat g * tqFam q σ i = mat g' * tqFam q σ i') : i = i' := by
  by_cases hi : (i : ℕ) < q <;> by_cases hi' : (i' : ℕ) < q
  · have h2 := cancel_left g g' h
    rw [tqFam_lt σ i hi, tqFam_lt σ i' hi'] at h2
    exact Fin.ext (upper_rel hi hi' _ h2)
  · have h2 := cancel_left g g' h
    rw [tqFam_lt σ i hi, tqFam_ge σ i' hi'] at h2
    exact (not_upper_eq_diag hq _ _ h2).elim
  · have h2 := cancel_left g' g h.symm
    rw [tqFam_lt σ i' hi', tqFam_ge σ i hi] at h2
    exact (not_upper_eq_diag hq _ _ h2).elim
  · have := i.isLt
    have := i'.isLt
    exact Fin.ext (by omega)

lemma diag_mem {N l q : ℕ} (hq : q.Prime) (hqNl : ¬ q ∣ N * l) (hqN : IsUnit (q : ZMod N))
    (σ : SL(2, ℤ)) (hσ : IsDiam N l (q : ZMod N) σ) :
    ∃ γ₁ γ₂ : Lev N l, mat σ * dg q 1 = mat γ₁ * dg 1 q * mat γ₂ := by
  have := Fact.mk hq
  obtain ⟨hs10N, hs10l, hs11, hs00⟩ := diam_facts hσ
  have hσd := sl2_entry_det_eq_one σ
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = ((N * l : ℕ) : ℤ) := ⟨_, rfl⟩
  have hnN : ((n : ℤ) : ZMod N) = 0 := by rw [hn]; push_cast; simp
  have hnl : ((n : ℤ) : ZMod l) = 0 := by rw [hn]; push_cast; simp
  have hnq : ((n : ℤ) : ZMod q) ≠ 0 := by
    rw [hn, Int.cast_natCast, Ne, CharP.cast_eq_zero_iff (ZMod q) q]
    exact hqNl
  have hqq : ((q : ℕ) : ZMod q) = 0 := ZMod.natCast_self q
  have hdetM : (mat σ 0 0 * q + mat σ 0 1 * n) * mat σ 1 1 - mat σ 0 1 * (mat σ 1 0 * q + mat σ 1 1 * n) = q := by
    linear_combination (q : ℤ) * hσd
  have haM : ((mat σ 0 0 * q + mat σ 0 1 * n : ℤ) : ZMod N) = 1 := by
    push_cast
    linear_combination hs00 + ((mat σ 0 1 : ℤ) : ZMod N) * hnN
  have hcM : ((mat σ 1 0 * q + mat σ 1 1 * n : ℤ) : ZMod N) = 0 := by
    push_cast
    linear_combination (q : ZMod N) * hs10N + ((mat σ 1 1 : ℤ) : ZMod N) * hnN
  have hclM : ((mat σ 1 0 * q + mat σ 1 1 * n : ℤ) : ZMod l) = 0 := by
    push_cast
    linear_combination (q : ZMod l) * hs10l + ((mat σ 1 1 : ℤ) : ZMod l) * hnl
  have hndM : ¬ (((mat σ 0 0 * q + mat σ 0 1 * n : ℤ) : ZMod q) = 0 ∧ ((mat σ 1 0 * q + mat σ 1 1 * n : ℤ) : ZMod q) = 0) := by
    rintro ⟨h1, h2⟩
    push_cast at h1 h2
    have h1' : ((mat σ 0 1 : ℤ) : ZMod q) * (n : ZMod q) = 0 := by linear_combination h1 - ((mat σ 0 0 : ℤ) : ZMod q) * hqq
    have h2' : ((mat σ 1 1 : ℤ) : ZMod q) * (n : ZMod q) = 0 := by linear_combination h2 - ((mat σ 1 0 : ℤ) : ZMod q) * hqq
    have hs01 := (mul_eq_zero.1 h1').resolve_right hnq
    have hs11q := (mul_eq_zero.1 h2').resolve_right hnq
    have e := congrArg (Int.cast : ℤ → ZMod q) hσd
    push_cast at e
    exact one_ne_zero (by linear_combination -e + ((mat σ 0 0 : ℤ) : ZMod q) * hs11q - ((mat σ 1 0 : ℤ) : ZMod q) * hs01 : (1 : ZMod q) = 0)
  obtain ⟨j, -, γ, hγ, hM⟩ := exists_upper hq hqN
    !![mat σ 0 0 * q + mat σ 0 1 * n, mat σ 0 1; mat σ 1 0 * q + mat σ 1 1 * n, mat σ 1 1] hdetM haM hcM hclM hndM
  have hdet2 : (1 - (j : ℤ) * n) * 1 - (j : ℤ) * (-n) = 1 := by ring
  refine ⟨⟨γ, hγ⟩, ⟨slMk (1 - (j : ℤ) * n) j (-n) 1 hdet2, slMk_mem_lev hdet2 ?_ (by simp) ?_ ?_⟩, ?_⟩
  · push_cast
    linear_combination -((j : ZMod N)) * hnN
  · push_cast
    linear_combination -hnN
  · push_cast
    linear_combination -hnl
  · have hUV : dg 1 q * mat (slMk (1 - (j : ℤ) * n) j (-n) 1 hdet2) =
        !![1, (j : ℤ); 0, (q : ℤ)] * !![1, 0; -n, 1] := by
      rw [mat_slMk]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    show mat σ * dg q 1 = mat γ * dg 1 q * mat (slMk (1 - (j : ℤ) * n) j (-n) 1 hdet2)
    rw [Matrix.mul_assoc, hUV, ← Matrix.mul_assoc, ← hM]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tq_reps {N l q : ℕ} (hq : q.Prime) (hqNl : ¬ q ∣ N * l) (σ : SL(2, ℤ))
    (hσ : IsDiam N l (q : ZMod N) σ) : IsDCReps (Lev N l) (dg 1 q) (tqFam q σ) := by
  have := Fact.mk hq
  have hqN : IsUnit (q : ZMod N) := (ZMod.isUnit_iff_coprime q N).2
    ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_left h l))
  have hql : IsUnit (q : ZMod l) := (ZMod.isUnit_iff_coprime q l).2
    ((Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqNl (dvd_mul_of_dvd_right h N))
  refine ⟨fun i => ?_, fun γ₁ γ₂ => ?_⟩
  · by_cases hi : (i : ℕ) < q
    · rw [tqFam_lt σ i hi]
      exact upper_mem N l q i
    · rw [tqFam_ge σ i hi]
      exact diag_mem hq hqNl hqN σ hσ
  · obtain ⟨hdet, ha, hc, hcl⟩ := dc_entries q γ₁ γ₂ γ₁.2 γ₂.2
    have key : ∃ i, ∃ γ : Lev N l, mat γ₁ * dg 1 q * mat γ₂ = mat γ * tqFam q σ i := by
      by_cases hnd : (((mat γ₁ * dg 1 q * mat γ₂) 0 0 : ℤ) : ZMod q) = 0 ∧
          (((mat γ₁ * dg 1 q * mat γ₂) 1 0 : ℤ) : ZMod q) = 0
      · obtain ⟨γ, hγ, hM⟩ := diam_case hq.ne_zero hqN hql σ hσ _ hdet ha hc hcl
          ((CharP.intCast_eq_zero_iff (ZMod q) q _).1 hnd.1) ((CharP.intCast_eq_zero_iff (ZMod q) q _).1 hnd.2)
        exact ⟨Fin.last q, ⟨γ, hγ⟩, by rw [tqFam_ge σ _ (by simp)]; exact hM⟩
      · obtain ⟨j, hj, γ, hγ, hM⟩ := exists_upper hq hqN _ hdet ha hc hcl hnd
        exact ⟨⟨j, by omega⟩, ⟨γ, hγ⟩, by rw [tqFam_lt σ _ hj]; exact hM⟩
    obtain ⟨i, γ, hγ⟩ := key
    exact ⟨i, ⟨γ, hγ⟩, fun i' ⟨γ', hγ'⟩ => tq_inj hq σ γ' γ i' i (hγ'.symm.trans hγ)⟩

private lemma mul_dg_mul_entry_ne_zero_mod_prime (l : ℕ) [Fact l.Prime] (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1)
    (hA10 : ((A 1 0 : ℤ) : ZMod l) = 0) (hB10 : ((B 1 0 : ℤ) : ZMod l) = 0) :
    (((A * dg 1 l * B) 0 0 : ℤ) : ZMod l) ≠ 0 := by
  have h00 : (A * dg 1 l * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * l * B 1 0 := by
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have hA0 : ((A 0 0 : ℤ) : ZMod l) ≠ 0 := fun h0 => by
    have e := congrArg (Int.cast : ℤ → ZMod l) hA
    push_cast at e
    exact one_ne_zero (by linear_combination -e + ((A 1 1 : ℤ) : ZMod l) * h0 - ((A 0 1 : ℤ) : ZMod l) * hA10 : (1 : ZMod l) = 0)
  have hB0 : ((B 0 0 : ℤ) : ZMod l) ≠ 0 := fun h0 => by
    have e := congrArg (Int.cast : ℤ → ZMod l) hB
    push_cast at e
    exact one_ne_zero (by linear_combination -e + ((B 1 1 : ℤ) : ZMod l) * h0 - ((B 0 1 : ℤ) : ZMod l) * hB10 : (1 : ZMod l) = 0)
  rw [h00]
  push_cast
  rw [ZMod.natCast_self, mul_zero, zero_mul, add_zero]
  exact mul_ne_zero hA0 hB0

theorem ul_reps {N l : ℕ} (hl : l.Prime) (hlN : ¬ l ∣ N) : IsDCReps (Lev N l) (dg 1 l) (ulFam l) := by
  have := Fact.mk hl
  have hlN' : IsUnit (l : ZMod N) := (ZMod.isUnit_iff_coprime l N).2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN)
  refine ⟨fun i => upper_mem N l l i, fun γ₁ γ₂ => ?_⟩
  obtain ⟨hdet, ha, hc, hcl⟩ := dc_entries l γ₁ γ₂ γ₁.2 γ₂.2
  have h₁ := γ₁.2
  have h₂ := γ₂.2
  rw [lev_iff] at h₁ h₂
  have hx := mul_dg_mul_entry_ne_zero_mod_prime l (mat γ₁) (mat γ₂) (sl2_entry_det_eq_one γ₁) (sl2_entry_det_eq_one γ₂) h₁.2.2.2 h₂.2.2.2
  obtain ⟨j, hj, γ, hγ, hM⟩ := exists_upper hl hlN' _ hdet ha hc hcl (fun h => hx h.1)
  refine ⟨⟨j, hj⟩, ⟨⟨γ, hγ⟩, hM⟩, fun i' ⟨γ', hγ'⟩ => ?_⟩
  have h2 := cancel_left γ' γ (hγ'.symm.trans hM)
  exact Fin.ext (upper_rel i'.2 hj _ h2)

lemma diam_conj {N l : ℕ} {d : ZMod N} {σ : SL(2, ℤ)} (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  obtain ⟨hs10N, hs10l, -, -⟩ := diam_facts hσ
  have eN := congrArg (Int.cast : ℤ → ZMod N) (sl2_entry_det_eq_one σ)
  push_cast at eN
  rw [lev_iff] at hγ ⊢
  obtain ⟨g00, g11, g10, g10l⟩ := hγ
  have hinv : mat σ⁻¹ = !![mat σ 1 1, -mat σ 0 1; -mat σ 1 0, mat σ 0 0] := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i k
    fin_cases i <;> fin_cases k <;> rfl
  have hP00 : mat (σ * γ * σ⁻¹) 0 0 = (mat σ 0 0 * mat γ 0 0 + mat σ 0 1 * mat γ 1 0) * mat σ 1 1 -
      (mat σ 0 0 * mat γ 0 1 + mat σ 0 1 * mat γ 1 1) * mat σ 1 0 := by
    rw [mat_mul', mat_mul', hinv]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hP10 : mat (σ * γ * σ⁻¹) 1 0 = (mat σ 1 0 * mat γ 0 0 + mat σ 1 1 * mat γ 1 0) * mat σ 1 1 -
      (mat σ 1 0 * mat γ 0 1 + mat σ 1 1 * mat γ 1 1) * mat σ 1 0 := by
    rw [mat_mul', mat_mul', hinv]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hP11 : mat (σ * γ * σ⁻¹) 1 1 = -((mat σ 1 0 * mat γ 0 0 + mat σ 1 1 * mat γ 1 0) * mat σ 0 1) +
      (mat σ 1 0 * mat γ 0 1 + mat σ 1 1 * mat γ 1 1) * mat σ 0 0 := by
    rw [mat_mul', mat_mul', hinv]
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hP00, hP10, hP11]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> push_cast
  · linear_combination ((mat σ 0 0 : ℤ) : ZMod N) * ((mat σ 1 1 : ℤ) : ZMod N) * g00 + eN + ((mat σ 0 1 : ℤ) : ZMod N) * ((mat σ 1 1 : ℤ) : ZMod N) * g10 + (((mat σ 0 1 : ℤ) : ZMod N) - ((mat σ 0 0 : ℤ) : ZMod N) * ((mat γ 0 1 : ℤ) : ZMod N) - ((mat σ 0 1 : ℤ) : ZMod N) * ((mat γ 1 1 : ℤ) : ZMod N)) * hs10N
  · linear_combination ((mat σ 1 1 : ℤ) : ZMod N) * ((mat σ 0 0 : ℤ) : ZMod N) * g11 + eN - ((mat σ 1 1 : ℤ) : ZMod N) * ((mat σ 0 1 : ℤ) : ZMod N) * g10 + (((mat σ 0 1 : ℤ) : ZMod N) - ((mat γ 0 0 : ℤ) : ZMod N) * ((mat σ 0 1 : ℤ) : ZMod N) + ((mat γ 0 1 : ℤ) : ZMod N) * ((mat σ 0 0 : ℤ) : ZMod N)) * hs10N
  · linear_combination (((mat γ 0 0 : ℤ) : ZMod N) * ((mat σ 1 1 : ℤ) : ZMod N) - ((mat σ 1 0 : ℤ) : ZMod N) * ((mat γ 0 1 : ℤ) : ZMod N) - ((mat σ 1 1 : ℤ) : ZMod N) * ((mat γ 1 1 : ℤ) : ZMod N)) * hs10N + ((mat σ 1 1 : ℤ) : ZMod N) * ((mat σ 1 1 : ℤ) : ZMod N) * g10
  · linear_combination (((mat γ 0 0 : ℤ) : ZMod l) * ((mat σ 1 1 : ℤ) : ZMod l) - ((mat σ 1 0 : ℤ) : ZMod l) * ((mat γ 0 1 : ℤ) : ZMod l) - ((mat σ 1 1 : ℤ) : ZMod l) * ((mat γ 1 1 : ℤ) : ZMod l)) * hs10l + ((mat σ 1 1 : ℤ) : ZMod l) * ((mat σ 1 1 : ℤ) : ZMod l) * g10l

theorem diam_reps {N l : ℕ} (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) :
    IsDCReps (Lev N l) (mat σ) (fun _ : Unit => mat σ) := by
  refine ⟨fun _ => ⟨1, 1, by simp⟩, fun γ₁ γ₂ => ⟨(), ⟨⟨(γ₁ : SL(2, ℤ)) * (σ * (γ₂ : SL(2, ℤ)) * σ⁻¹),
    mul_mem γ₁.2 (diam_conj hσ γ₂ γ₂.2)⟩, ?_⟩, fun _ _ => rfl⟩⟩
  simp only [← mat_mul']
  congr 1
  show (γ₁ : SL(2, ℤ)) * σ * γ₂ = (γ₁ : SL(2, ℤ)) * (σ * (γ₂ : SL(2, ℤ)) * σ⁻¹) * σ
  group

theorem dcReps_level : ∀ (N l : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ → IsDCReps (Lev N l) (dg 1 q) (tqFam q σ)) ∧ IsDCReps (Lev N l) (dg 1 l) (ulFam l) ∧ ∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → IsDCReps (Lev N l) (mat σ) (fun _ : Unit => mat σ) := by
  intro N l _ hl hlN
  exact ⟨fun q σ hq hqNl hσ => tq_reps hq hqNl σ hσ, ul_reps hl hlN, fun d σ hσ => diam_reps d σ hσ⟩

end GlobalTheory.HeckeFamilyMatrices.CosetReps
