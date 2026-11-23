import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

noncomputable section

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def tGL {n : ℕ} (i j : Fin n) (h : i ≠ j) (s : ℂ) : GL (Fin n) ℂ :=
  ⟨transvection i j s, transvection i j (-s),
    by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem inv_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (s : ℂ) (T : GL (Fin n) ℂ)
    (hT : T.val = transvection i j s) : (T⁻¹).val = transvection i j (-s) := by
  have e : T = tGL i j h s := Units.ext hT
  subst e
  rfl

theorem eval_evalRingHom {σ : Type} (g : σ → ℂ[X]) (Q : MvPolynomial σ ℂ) (s : ℂ) :
    (MvPolynomial.aeval g Q).eval s = MvPolynomial.eval (fun v => (g v).eval s) Q := by
  rw [MvPolynomial.aeval_def, ← Polynomial.coe_evalRingHom, MvPolynomial.eval₂_comp_left]
  have : (Polynomial.evalRingHom s).comp (algebraMap ℂ ℂ[X]) = RingHom.id ℂ := by
    ext; simp
  rw [this]
  rfl

theorem expand {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ)
    (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j) (w : ι → ℂ) :
    ∃ q : ι → ℂ[X], ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s := by
  choose Q hQ using hΦ.poly
  let g : (Fin n × Fin n) ⊕ (Fin n × Fin n) → ℂ[X] :=
    Sum.elim (fun p => (transvection i j (X : ℂ[X])) p.1 p.2)
      (fun p => (transvection i j (-X : ℂ[X])) p.1 p.2)
  refine ⟨fun a => ∑ b, MvPolynomial.aeval g (Q a b) * C (w b), ?_⟩
  intro s T hT
  funext a
  simp only [mulVec, dotProduct, eval_finset_sum, eval_mul, eval_C, eval_evalRingHom]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hQ a b T]
  congr 2
  congr 1
  funext v
  rcases v with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · simp only [g, Sum.elim_inl, hT, transvection, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp
  · simp only [g, Sum.elim_inr, inv_val h s T hT, transvection, Matrix.add_apply,
      Matrix.one_apply, Matrix.single_apply]
    split_ifs <;> simp

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

theorem diagonal_eq_of_isDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsDiag) :
    A = diagonal (fun m => A m m) := by
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [diagonal_apply_ne _ hab, hA hab]

theorem diag_ne_zero {n : ℕ} (D : GL (Fin n) ℂ) (hD : D.val.IsDiag) (m : Fin n) :
    D.val m m ≠ 0 := by
  have hdet : (D.val).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp D.isUnit).ne_zero
  rw [diagonal_eq_of_isDiag _ hD, det_diagonal] at hdet
  exact (Finset.prod_ne_zero_iff.mp hdet) m (Finset.mem_univ _)

theorem diagonal_mul_transvection {n : ℕ} {i j : Fin n} (h : i ≠ j) (d : Fin n → ℂ)
    (hdj : d j ≠ 0) (s : ℂ) :
    diagonal d * transvection i j s = transvection i j (s * (d i / d j)) * diagonal d := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.add_apply, diagonal_mul, mul_diagonal, Matrix.single_apply]
  by_cases h2 : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [and_self, if_true, one_apply_ne h]
    field_simp
    ring
  · simp only [h2, if_false, mul_zero, zero_mul, add_zero]
    by_cases hab : a = b
    · subst hab; simp
    · simp [one_apply_ne hab]

theorem conj_val {n : ℕ} {i j : Fin n} (h : i ≠ j) (D : GL (Fin n) ℂ) (hD : D.val.IsDiag)
    (s : ℂ) (T : GL (Fin n) ℂ) (hT : T.val = transvection i j s) :
    (D * T * D⁻¹).val = transvection i j (s * (D.val i i / D.val j j)) := by
  have key : D.val * T.val = transvection i j (s * (D.val i i / D.val j j)) * D.val := by
    have := diagonal_mul_transvection h (fun m => D.val m m) (diag_ne_zero D hD j) s
    rw [← diagonal_eq_of_isDiag _ hD] at this
    rw [hT]
    exact this
  rw [Units.val_mul, Units.val_mul, key, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW.LowerTransv

open Polynomial

def shiftWt {n : ℕ} (ν : Fin n → ℤ) (i j : Fin n) (k : ℕ) : Fin n → ℤ :=
  fun m => ν m + (k : ℤ) * (if m = i then 1 else 0) - (k : ℤ) * (if m = j then 1 else 0)

theorem prod_zpow_shiftWt {n : ℕ} (d : Fin n → ℂ) (hd : ∀ m, d m ≠ 0) (ν : Fin n → ℤ)
    (i j : Fin n) (k : ℕ) :
    ∏ m, d m ^ (shiftWt ν i j k m) = (∏ m, d m ^ ν m) * (d i / d j) ^ k := by
  have e : ∀ m, d m ^ (shiftWt ν i j k m) =
      d m ^ ν m * ((if m = i then d m ^ (k : ℤ) else 1) / (if m = j then d m ^ (k : ℤ) else 1)) := by
    intro m
    simp only [shiftWt]
    rw [zpow_sub₀ (hd m), zpow_add₀ (hd m), mul_div_assoc]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun m _ => e m), Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp [div_pow, zpow_natCast]

theorem domLE_shiftWt {n : ℕ} {ν lam : Fin n → ℤ} (hν : DomLE ν lam) {i j : Fin n} (hji : j < i)
    (k : ℕ) : DomLE (shiftWt ν i j k) lam := by
  obtain ⟨h1, h2⟩ := hν
  constructor
  · rw [← h1]
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro K
    have hK := h2 K
    simp only [shiftWt, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    have hji' : (j : ℕ) < i := hji
    by_cases hi : (i : ℕ) < K
    · have hj : (j : ℕ) < K := lt_trans hji' hi
      simp only [hi, hj, if_true]
      linarith
    · simp only [hi, if_false, mul_zero, add_zero]
      have : (0 : ℤ) ≤ (k : ℤ) * (if (j : ℕ) < K then 1 else 0) := by
        split_ifs <;> simp
      linarith

theorem isWtVec_coeff {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (hΦ : IsPolyRep Φ) {i j : Fin n} (h : i ≠ j)
    (ν : Fin n → ℤ) (w : ι → ℂ) (hw : IsWtVec Φ ν w) (q : ι → ℂ[X])
    (hq : ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s →
      Φ T *ᵥ w = fun a => (q a).eval s) (k : ℕ) :
    IsWtVec Φ (shiftWt ν i j k) (fun a => (q a).coeff k) := by
  intro D hD
  have hd : ∀ m, D.val m m ≠ 0 := diag_ne_zero D hD
  set c : ℂ := D.val i i / D.val j j with hc
  set P : ℂ := ∏ m, D.val m m ^ ν m with hP
  have hs : ∀ s : ℂ, Φ D *ᵥ (fun a => (q a).eval s) = P • (fun a => (q a).eval (s * c)) := by
    intro s
    have hT : (tGL i j h s).val = transvection i j s := rfl
    have hc' : Φ D * Φ (tGL i j h s) = Φ (D * tGL i j h s * D⁻¹) * Φ D := by
      rw [← hΦ.mul, ← hΦ.mul, inv_mul_cancel_right]
    rw [← hq s _ hT, ← hq (s * c) _ (conj_val h D hD s _ hT), mulVec_mulVec, hc',
      ← mulVec_mulVec, hw D hD, mulVec_smul]
  have hpoly : ∀ a, ∑ b, C (Φ D a b) * q b = C P * (q a).comp (C c * X) := by
    intro a
    apply Polynomial.funext
    intro s
    have e := congrFun (hs s) a
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e
    simp only [eval_finset_sum, eval_mul, eval_C, eval_comp, eval_X]
    rw [e, mul_comm c s]
  funext a
  have e := congrArg (fun p => Polynomial.coeff p k) (hpoly a)
  simp only [finset_sum_coeff, coeff_C_mul, comp_C_mul_X_coeff] at e
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e, prod_zpow_shiftWt _ hd]
  ring

end GlobalTheory.AlgWtHW.LowerTransv

namespace GlobalTheory.AlgWtHW

open Polynomial LowerTransv

theorem lowerTransvection_mulVec_mem_Sle : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam →
    ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ),
    T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ lam ν hν w hw i j hji s T hT
  have h : i ≠ j := hji.ne'
  obtain ⟨q, hq⟩ := expand Φ hΦ h w
  set N : ℕ := (Finset.univ.sup fun a => (q a).natDegree) + 1 with hN
  have hsum : Φ T *ᵥ w = ∑ k ∈ Finset.range N, s ^ k • (fun a => (q a).coeff k) := by
    rw [hq s T hT]
    funext a
    rw [Finset.sum_apply]
    have hlt : (q a).natDegree < N :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun a => (q a).natDegree) (Finset.mem_univ a))
    rw [eval_eq_sum_range' hlt]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨shiftWt ν i j k, domLE_shiftWt hν hji k, isWtVec_coeff Φ hΦ h ν w hw q hq k⟩

end GlobalTheory.AlgWtHW
