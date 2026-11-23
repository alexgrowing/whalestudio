import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTvalNeZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSlopeSqLocalMatricesEqDeterminantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatCharPowEqDetPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylGramDeterminantLeDimPowDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibSlope

section Log

variable {K : Type} [Field K] {φ : K → ℝ} (hφ : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
include hφ

theorem log_one : φ 1 = 0 := by
  have := hφ 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

theorem log_prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    φ (∏ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using log_one hφ
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, hφ _ _ (hf i) (Finset.prod_ne_zero_iff.2 fun j _ => hf j), ih]

theorem log_pow {x : K} (hx : x ≠ 0) (n : ℕ) : φ (x ^ n) = n * φ x := by
  have := log_prod hφ (Finset.range n) (fun _ => x) fun _ => hx
  simpa using this

theorem log_det_rhoMat [CharZero K] {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) {g : Matrix (Fin n) (Fin n) K}
    (hg : g.det ≠ 0) : (rhoMat la g).det ≠ 0 ∧
      φ (rhoMat la g).det = (dim la : ℝ) * ((size la : ℝ) / (n : ℝ) * φ g.det) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim g 1, GlobalTheory.DefPt.Model.rhoMat_one, Matrix.det_one, log_one hφ]
    simp
  · have h := det_rhoMat_pow K n la hla g
    have h0 : (rhoMat la g).det ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at h
      exact pow_ne_zero _ hg h.symm
    refine ⟨h0, ?_⟩
    have h1 := congrArg φ h
    rw [log_pow hφ h0, log_pow hφ hg] at h1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast at h1
    field_simp
    linarith

theorem log_det_kron {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] {c : K} (hc : c ≠ 0) (M : ∀ t, Matrix (J t) (J t) K) (hM : ∀ t, (M t).det ≠ 0)
    (r : T → ℝ) (hr : ∀ t, φ (M t).det = Fintype.card (J t) * r t) :
    (c • kron M).det ≠ 0 ∧ φ (c • kron M).det = Fintype.card (∀ t, J t) * (φ c + ∑ t, r t) := by
  have hk := (kronFamily_mul_one_det T J K M M).2.2
  have hp : ∀ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) ≠ 0 := fun t => pow_ne_zero _ (hM t)
  have h0 : (kron M).det ≠ 0 := hk ▸ Finset.prod_ne_zero_iff.2 fun t _ => hp t
  rw [Matrix.det_smul]
  refine ⟨mul_ne_zero (pow_ne_zero _ hc) h0, ?_⟩
  rw [hφ _ _ (pow_ne_zero _ hc) h0, log_pow hφ hc, hk, log_prod hφ _ _ hp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [log_pow hφ (hM t), hr, ← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ t),
    Fintype.card_pi]

end Log

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul_real (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (vAdd w (x * y) : ℝ) = vAdd w x + vAdd w y := by
  have h1 : w.valuation K x ≠ 0 := by simpa using hx
  have h2 : w.valuation K y ≠ 0 := by simpa using hy
  rw [← Int.cast_add, vAdd, vAdd, vAdd, map_mul, WithZero.log_mul h1 h2, neg_add]

theorem valuation_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K}
    (hM : IntAt w M) : w.valuation K M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun i _ => hM _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem finite_vAdd_det {ι : Type} [Fintype ι] [DecidableEq ι] {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K}
    (hA : IsAdelic A) : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
  refine hA.2.subset fun w hw h => hw ?_
  have h1 := valuation_det_le w h.1
  have h2 := valuation_det_le w h.2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀] at h2
  have h0 : w.valuation K (A w).det ≠ 0 := by simpa using hA.1 w
  have h3 : w.valuation K (A w).det = 1 :=
    le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  simp [vAdd, h3]

end Val

theorem log_norm_mul (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {la : ∀ t, Fin (N t) → ℕ}

theorem vAdd_det_fibA {K : Type} [Field K] [NumberField K] (hla : ∀ t, Antitone (la t)) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) {B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K} (hB : ∀ t, (B t).det ≠ 0) :
    (vAdd w (fibA la a B).det : ℝ) =
      Fintype.card (TIdx la) * (vAdd w a + ∑ t, (size (la t) : ℝ) / (N t : ℝ) * vAdd w (B t).det) :=
  (log_det_kron (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) ha _
    (fun t => (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).1) _
    (fun t => by
      rw [← dim_eq_card]
      exact (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).2)).2

theorem log_det_fibY (hla : ∀ t, Antitone (la t)) {s : ℝ} (hs : 0 < s) {X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ}
    (hX : ∀ t, (X t).det ≠ 0) : (fibY la s X).det ≠ 0 ∧ Real.log ‖(fibY la s X).det‖ =
      Fintype.card (TIdx la) * (Real.log s + ∑ t, (Real.log ‖(onMat (la t)).det‖ / dim (la t) +
        (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)) := by
  have hρ := fun t => log_det_rhoMat (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (hla t) (hX t)
  have ho := fun t => (GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ (la t) (hla t)).1
  have h := log_det_kron (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (c := (s : ℂ))
    (Complex.ofReal_ne_zero.2 hs.ne') (fun t => onMat (la t) * rhoMat (la t) (X t))
    (fun t => by rw [Matrix.det_mul]; exact mul_ne_zero (ho t) (hρ t).1)
    (fun t => Real.log ‖(onMat (la t)).det‖ / dim (la t) + (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)
    (fun t => by
      have hd : (dim (la t) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos (hla t)).ne'
      have h2 := (hρ t).2
      rw [← dim_eq_card, Matrix.det_mul, log_norm_mul _ _ (ho t) (hρ t).1, h2, mul_add, mul_div_cancel₀ _ hd])
  simp only [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  exact h

theorem log_det_onMat_le {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) :
    Real.log ‖(onMat la).det‖ / dim la ≤ Real.log (dim la) / 2 := by
  obtain ⟨h0, h⟩ := GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ la hla
  have hd : (0 : ℝ) < dim la := Nat.cast_pos.2 (dim_pos hla)
  have h1 := Real.log_le_log (pow_pos (norm_pos_iff.2 h0) 2) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_le_iff₀ hd]
  push_cast at h1
  linarith

theorem slope_fibre_ge : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  intro K _ _ _ T _ _ N la hla a B s X ha hfa hB hs hX hsc hXc
  have hY := fun σ => log_det_fibY hla (hs σ) (hX σ)
  refine ⟨fun σ => (hY σ).1, ?_⟩
  have hD : 0 < Fintype.card (TIdx la) := by
    rw [Fintype.card_pi]
    exact Finset.prod_pos fun t _ => dim_eq_card (la t) ▸ dim_pos (hla t)
  haveI : Nonempty (TIdx la) := Fintype.card_pos_iff.1 hD
  have hD' : (Fintype.card (TIdx la) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hK : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants K (TIdx la) _ _ (GlobalTheory.FibAdel.fibA_isAdelic K T N la a B ha hfa hB) (fun σ => (hY σ).1)
    (fun σ => Real.log_injOn_pos (norm_pos_iff.2 (hY _).1) (norm_pos_iff.2 (hY _).1) (by
      rw [(hY _).2, (hY _).2]; simp only [hsc, hXc]))]
  have hfa' : (Function.support fun w => (vAdd w (a w) : ℝ)).Finite := hfa.subset fun w hw h => hw (by
    simp only at h ⊢; rw [h, Int.cast_zero])
  have hfB := fun t => finite_vAdd_det (hB t)
  have hfin : ∑ᶠ w, (vAdd w (fibA la (a w) (B w)).det : ℝ) * lw K w = Fintype.card (TIdx la) *
      (∑ᶠ w, (vAdd w (a w) : ℝ) * lw K w +
        ∑ t, (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) := by
    have hsub : ∀ t, (Function.support fun w => (size (la t) : ℝ) / (N t : ℝ) *
        ((vAdd w (B w t).det : ℝ) * lw K w)).Finite := fun t =>
      (fin_mul (hfB t) (lw K)).subset (Function.support_mul_subset_right _ _)
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ _ (fun t _ => hsub t), ← finsum_add_distrib (fin_mul hfa' _), mul_finsum]
    · refine finsum_congr fun w => ?_
      rw [vAdd_det_fibA hla w (ha w) (fun t => (hB t).1 w), mul_assoc, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · exact (Set.finite_iUnion hsub).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (Finset.sum_eq_zero fun t _ => hn t)
  have hinf : ∑ σ, Real.log ‖(fibY la (s σ) (X σ)).det‖ = Fintype.card (TIdx la) *
      (∑ σ, Real.log (s σ) + ∑ t, (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖)) := by
    simp only [(hY _).2]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
      Finset.mul_sum]
  simp only [detDeg, lineDeg]
  rw [hfin, hinf]
  have key : ∀ u v : ℝ, 2 * (Fintype.card (TIdx la) * u - Fintype.card (TIdx la) * v / finrank ℚ K) /
      (Fintype.card (TIdx la) : ℝ) / 2 = u - v / finrank ℚ K := fun u v => by field_simp
  rw [key, add_div, Finset.sum_div (ι := T)]
  have hle : ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ((∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) -
      (∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) - Real.log (dim (la t)) / 2) ≤
      ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w -
        (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) :=
    Finset.sum_le_sum fun t _ => by
      have := log_det_onMat_le (hla t)
      rw [add_div, mul_div_cancel_left₀ _ hK.ne', mul_sub, mul_div_assoc]
      linarith
  rw [Finset.sum_sub_distrib (f := fun t => (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w)]
    at hle
  linarith

end GlobalTheory.FibSlope

end
