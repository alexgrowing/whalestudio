import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialRepTransvectionEntries
open Matrix GlobalTheory.AlgWtHW

namespace GlobalTheory.UnipotentWeights

noncomputable def tGL {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j c, transvection i j (-c),
    by rw [transvection_mul_transvection_same i j h]; simp,
    by rw [transvection_mul_transvection_same i j h]; simp⟩

theorem diag_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * d i / d j) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    diagonal_mul, mul_diagonal, single_apply, one_apply]
  by_cases ha : i = a <;> by_cases hb : j = b
  · subst ha hb; simp [h]; field_simp [hd j]
  · by_cases hab : a = b <;> simp [ha, hb, hab]
  · subst hb; by_cases hab : a = j
    · subst hab; simp [h]
    · simp [ha, hab]
  · by_cases hab : a = b <;> simp [ha, hb, hab]

theorem poly_coeff_eq (K : ℕ) (x y : ℕ → ℂ) (hxy : ∀ s : ℂ, ∑ k ∈ Finset.range (K + 1), s ^ k * x k =
    ∑ k ∈ Finset.range (K + 1), s ^ k * y k) (k : ℕ) (hk : k ≤ K) : x k = y k := by
  let Q : Polynomial ℂ := ∑ k ∈ Finset.range (K + 1), Polynomial.C (x k - y k) * Polynomial.X ^ k
  have hQ : Q = 0 := by
    apply Polynomial.funext
    intro s
    simp only [Q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    have := hxy s
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => by ring
  have hc := congrArg (fun p => Polynomial.coeff p k) hQ
  simp only [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_eq_single k] at hc
  · simpa [sub_eq_zero] using hc
  · intro m _ hm; simp [Ne.symm hm]
  · intro hk'; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) hk'

end GlobalTheory.UnipotentWeights

namespace GlobalTheory.UnipotentWeights

theorem prod_single_zpow {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ l, d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l) = d i := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem prod_wt_shift {n : ℕ} (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (i j : Fin n) (μ : Fin n → ℤ) (k : ℕ) :
    ∏ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      (∏ l, d l ^ μ l) * (d i / d j) ^ k := by
  have hpt : ∀ l, d l ^ ((μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1) : Fin n → ℤ) l) =
      d l ^ μ l * ((d l ^ ((Pi.single i (1 : ℤ) : Fin n → ℤ) l)) ^ k *
        ((d l ^ ((Pi.single j (1 : ℤ) : Fin n → ℤ) l)) ^ k)⁻¹) := by
    intro l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [zpow_add₀ (hd l), mul_sub, zpow_sub₀ (hd l), div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm ((Pi.single i (1:ℤ) : Fin n → ℤ) l), mul_comm ((Pi.single j (1:ℤ) : Fin n → ℤ) l)]
  simp_rw [hpt]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_pow,
    Finset.prod_pow, prod_single_zpow, prod_single_zpow, div_pow, div_eq_mul_inv]

end GlobalTheory.UnipotentWeights

namespace GlobalTheory

open GlobalTheory.UnipotentWeights in

theorem transvection_weightVec_expansion :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ →
      ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v →
        ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧
          (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧
          ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
            Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  intro n ι _ _ Φ hΦ i j hij μ v hv
  obtain ⟨P, hP⟩ := polyRep_transvection_entries_poly n ι Φ hΦ i j hij
  let K : ℕ := Finset.univ.sup (fun ab : ι × ι => (P ab.1 ab.2).natDegree)
  have hK : ∀ a b, (P a b).natDegree < K + 1 := fun a b =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun ab : ι × ι => (P ab.1 ab.2).natDegree) (Finset.mem_univ (a, b)))
  let w : ℕ → ι → ℂ := fun k a => ∑ b, (P a b).coeff k * v b
  have hexp : ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s →
      Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
    intro s B hB
    ext a
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, w]
    simp_rw [hP s B hB a, Polynomial.eval_eq_sum_range' (hK a _) s, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  refine ⟨K, w, ?_, ?_, hexp⟩
  · have h0 := hexp 0 1 (by simp)
    rw [hΦ.one, one_mulVec, Finset.sum_range_succ'] at h0
    simpa using h0.symm
  · intro k D hD
    by_cases hk : K < k
    · have hw : w k = 0 := by
        funext a
        simp only [w, Pi.zero_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hK a b) hk), zero_mul]
      rw [hw, mulVec_zero, smul_zero]
    push_neg at hk
    set d : Fin n → ℂ := fun l => D.val l l with hd_def
    have hDd : D.val = diagonal d := ((isDiag_iff_diagonal_diag _).1 hD).symm
    have hd : ∀ l, d l ≠ 0 := by
      have hdet : D.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 D.isUnit).ne_zero
      rw [hDd, det_diagonal, Finset.prod_ne_zero_iff] at hdet
      exact fun l => hdet l (Finset.mem_univ l)
    set lam : ℂ := ∏ l, D.val l l ^ μ l with hlam
    have hcomm : ∀ s : ℂ, D * tGL hij s = tGL hij (s * d i / d j) * D := by
      intro s
      ext1
      simp only [Units.val_mul, tGL]
      rw [hDd]
      exact diag_mul_transvection hij d hd s
    have hmain : ∀ s : ℂ, Φ D *ᵥ (∑ k ∈ Finset.range (K + 1), s ^ k • w k) =
        lam • ∑ k ∈ Finset.range (K + 1), (s * d i / d j) ^ k • w k := by
      intro s
      rw [← hexp s (tGL hij s) rfl, ← hexp _ (tGL hij (s * d i / d j)) rfl, mulVec_mulVec, ← hΦ.mul, hcomm,
        hΦ.mul, ← mulVec_mulVec, hv D hD, mulVec_smul]
    have hcoord : ∀ a, (Φ D *ᵥ w k) a = (lam * (d i / d j) ^ k) * w k a := by
      intro a
      refine poly_coeff_eq K (fun m => (Φ D *ᵥ w m) a) (fun m => (lam * (d i / d j) ^ m) * w m a) ?_ k hk
      intro s
      have := congrFun (hmain s) a
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum] at this
      rw [this]
      refine Finset.sum_congr rfl fun m _ => by ring
    ext a
    rw [hcoord a, Pi.smul_apply, smul_eq_mul, prod_wt_shift d hd i j μ k]

end GlobalTheory
