import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicHomogeneousOfKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.RealLift.SteepHarm

theorem eq_zero_of_euler_of_raise {σ : Type} [DecidableEq σ] (n : ℕ) (x : Fin n × Fin n → σ) (y : Fin n → σ) (hx : Function.Injective x)
    (f : MvPolynomial σ ℂ) (hE : ∑ i, X (y i) * pderiv (y i) f = f)
    (hK : ∀ k : Fin n, ∑ i, X (x (i, k)) * pderiv (y i) f = 0) : f = 0 := by
  set M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ) :=
    (rename x : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom.mapMatrix
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, ← RingHom.map_det]
    intro h0
    apply Matrix.det_mvPolynomialX_ne_zero (Fin n) ℂ
    apply rename_injective x hx
    simpa using h0
  have hv : Matrix.vecMul (fun i => pderiv (y i) f) M = 0 := by
    funext k
    rw [Pi.zero_apply, ← hK k]
    simp [Matrix.vecMul, dotProduct, hM, Matrix.mvPolynomialX, mul_comm]
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  rw [← hE]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show pderiv (y i) f = 0 from congrFun h0 i, mul_zero]

theorem fockAct2_Eab_apply {P Q R S : ℕ} (c d : Ix R S) (g : Pol P Q R S) :
    fockAct2 P Q R S (Eab c d) g = ∑ a : Ix P Q, (raiB (a, c) (lowB (a, d) g) +
      if c = d then (1 / 2 : ℂ) • g else 0) := by
  rw [fockAct2_Eab, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [omE, Prod.mk.injEq, true_and]
  split_ifs <;> simp

theorem not_hw_of_wFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (i : Fin R) (f : Pol P Q R S) (hi : P ≤ (i : ℕ))
    (hμ : μ (.inl i) = cPair P Q + 1)
    (hw : ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hPR : P ≤ R := hi.trans (Nat.le_of_lt i.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise P (fun p => ((.inl p.1, .inl (Fin.castLE hPR p.2)) : Ix P Q × Ix R S)) (fun i' => (.inl i', .inl i)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hPR h.2)
  · have h1 := hwt (.inl i)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl i) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hw, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inl (Fin.castLE hPR k)) (.inl i) (by
      show Fin.castLE hPR k < i
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inl (Fin.castLE hPR k) : Ix R S) ≠ Sum.inl i := by
      intro h; simp only [Sum.inl.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin Q, pderiv ((.inr x, .inl (Fin.castLE hPR k)) : Ix P Q × Ix R S) (X (.inr x, .inl i) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hw, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero] at h1
    exact h1

theorem not_hw_of_uFree (P Q R S : ℕ) (μ : Ix R S → ℚ) (j : Fin S) (f : Pol P Q R S) (hj : Q ≤ (j : ℕ))
    (hμ : μ (.inr j) = 1 - cPair P Q)
    (hu : ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0)
    (hf : IsHW (fockAct2 P Q R S) μ f) : False := by
  have hQS : Q ≤ S := hj.trans (Nat.le_of_lt j.2)
  obtain ⟨hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  obtain ⟨hwt, hpos⟩ := hmem
  apply hne
  refine eq_zero_of_euler_of_raise Q (fun p => ((.inr p.1, .inr (Fin.castLE hQS p.2)) : Ix P Q × Ix R S)) (fun j' => (.inr j', .inr j)) ?_ f ?_ ?_
  · intro p p' h
    simp only [Prod.mk.injEq, Sum.inr.injEq] at h
    exact Prod.ext h.1 (Fin.castLE_injective hQS h.2)
  · have h1 := hwt (.inr j)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr j) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = f := by
      intro x; rw [Derivation.leibniz, pderiv_X_self, hu, smul_zero, zero_add, smul_eq_mul, mul_one]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, hμ, cPair] at h1
    push_cast at h1
    linear_combination (norm := module) h1
  · intro k
    have h1 := hpos (.inr (Fin.castLE hQS k)) (.inr j) (by
      show Fin.castLE hQS k < j
      rw [Fin.lt_iff_val_lt_val]; simp; omega)
    rw [fockAct2_Eab_apply, Fintype.sum_sum_type] at h1
    simp only [raiB, lowB, linePos, if_true, if_false, Bool.false_eq_true] at h1
    have hne' : (Sum.inr (Fin.castLE hQS k) : Ix R S) ≠ Sum.inr j := by
      intro h; simp only [Sum.inr.injEq, Fin.ext_iff, Fin.coe_castLE] at h; omega
    have e1 : ∀ x : Fin P, pderiv ((.inl x, .inr (Fin.castLE hQS k)) : Ix P Q × Ix R S) (X (.inl x, .inr j) * f) = 0 := by
      intro x
      rw [Derivation.leibniz, pderiv_X_of_ne (by simp [hne'.symm]), hu, smul_zero, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe, e1, hne', if_false, add_zero,
      neg_zero, Finset.sum_const_zero, zero_add] at h1
    exact h1

theorem coeff_diag {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (α : σ →₀ ℕ) :
    coeff α (L f) = g α * coeff α f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial β c =>
    have : monomial β c = c • (monomial β (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, hL, coeff_smul, coeff_smul, coeff_smul, coeff_monomial]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [h]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem coeff_eig {σ : Type} (L : Module.End ℂ (MvPolynomial σ ℂ)) (g : (σ →₀ ℕ) → ℂ)
    (hL : ∀ α, L (monomial α 1) = g α • monomial α 1) (f : MvPolynomial σ ℂ) (c : ℂ) (hf : L f = c • f)
    (α : σ →₀ ℕ) (hα : coeff α f ≠ 0) : g α = c := by
  have h := coeff_diag L g hL f α
  rw [hf, coeff_smul, smul_eq_mul] at h
  exact (mul_right_cancel₀ hα h).symm

theorem trace_Eab_self {p q : ℕ} (a : Ix p q) : (Eab a a).trace = 1 := by
  simp [Eab, Matrix.trace_single_eq_same]

theorem monomial_facts (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ i' : Fin P, ∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) = x - cPair R S) ∧
    (∀ j' : Fin Q, ∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) = x + cPair R S) ∧
    (∀ k : Fin R, ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) = μ (.inl k) - cPair P Q) ∧
    (∀ l : Fin S, ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) = μ (.inr l) + cPair P Q) := by
  obtain ⟨_, hK, hne, hmem⟩ := hf
  rw [GlobalTheory.FockAlg.MinFirst.mem_hwSub] at hmem
  have e1 : ∀ a : Ix P Q, (∑ c, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (x : ℂ) := by
    intro a
    have h := hK (Eab a a) (GlobalTheory.FockAlg.MinFirst.isKC_diag a)
    rw [trace_Eab_self, mul_one] at h
    exact coeff_eig _ _ (fun β => cartan1 a β) f _ h α hα
  have e2 : ∀ c : Ix R S, (∑ a, lineSign a c * (((α (a, c) : ℕ) : ℂ) + 1 / 2)) = (μ c : ℂ) := by
    intro c
    have h := hmem.1 c
    rw [sub_eq_zero] at h
    exact coeff_eig _ _ (fun β => cartan2 c β) f _ h α hα
  refine ⟨fun i' => ?_, fun j' => ?_, fun k => ?_, fun l => ?_⟩
  · have h := e1 (.inl i')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ) + R / 2 - S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e1 (.inr j')
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ l : Fin S, (α (.inr j', .inr l) : ℚ) - ∑ k : Fin R, (α (.inr j', .inl k) : ℚ) - R / 2 + S / 2 : ℚ) : ℂ) = (x : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inl k)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ) + P / 2 - Q / 2 : ℚ) : ℂ) = (μ (.inl k) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith
  · have h := e2 (.inr l)
    simp only [Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    have h' : ((∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ) - ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ) - P / 2 + Q / 2 : ℚ) : ℂ) = (μ (.inr l) : ℂ) := by
      push_cast; rw [← h]; ring
    have h'' := Rat.cast_injective h'
    simp only [cPair]; linarith

theorem sum_fin_ite_lt (P R : ℕ) (hPR : P ≤ R) (a b : ℚ) :
    ∑ k : Fin R, (if (k : ℕ) < P then a else b) = P * a + ((R - P : ℕ) : ℚ) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < P then a else b) R]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hPR
  rw [Finset.sum_range_add]
  simp [Finset.sum_ite_of_true, Finset.sum_range]

theorem monomial_cols (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    ∑ y, (α y : ℚ) = degW (cPair P Q) μ := by
  obtain ⟨hh, _, hne, hmem⟩ := hf
  obtain ⟨W, fW, hP, sW⟩ := ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 f).1
  have hOT := ((GlobalTheory.BlockReps.finite_module_structure R S _ (fockAct2 P Q R S) GlobalTheory.FockAlg.MinFirst.kLie2 W fW sW
    fun v _ => GlobalTheory.FockAlg.MinFirst.wts2 v).2.2.2 μ f hP ⟨hne, hmem⟩).2.1
  obtain ⟨d, hd, hhom⟩ := (harmonic_homog_of_type P Q R S).2 μ f hne hOT hh
  rw [mem_homogeneousSubmodule] at hhom
  have h := hhom hα
  rw [← hd, ← h]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype]

theorem alpha_beta_ge_one (P Q P' Q' R S : ℕ) (κ : ℤ) (hN : GlobalTheory.RealLift.Num P Q P' Q' R S κ) :
    1 ≤ (κ : ℚ) / 2 - cPair R S ∧ 1 ≤ (κ : ℚ) / 2 + cPair R S := by
  obtain ⟨_, _, _, _, ⟨n, hn⟩, ⟨m, hm⟩, hκ⟩ := hN
  have hmn : (n : ℤ) + 1 ≤ m := by
    have : ((R + S : ℕ) : ℤ) = n + n := by exact_mod_cast hn
    omega
  have hmn' : (n : ℚ) + 1 ≤ m := by exact_mod_cast hmn
  have hκq : (κ : ℚ) = m + m := by exact_mod_cast hm
  have hnq : (R : ℚ) + S = n + n := by exact_mod_cast hn
  have hR : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hS : (0 : ℚ) ≤ S := Nat.cast_nonneg _
  simp only [cPair]
  constructor <;> linarith

theorem col_pure (P Q R S : ℕ) (x : ℚ) (μ : Ix R S → ℚ) (f : Pol P Q R S)
    (hf : GlobalTheory.RealLift.IsHarmVec x μ f) (α : (Ix P Q × Ix R S) →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ k : Fin R, 0 ≤ μ (.inl k) - cPair P Q → ∀ j' : Fin Q, α (.inr j', .inl k) = 0) ∧
    (∀ l : Fin S, 0 ≤ μ (.inr l) + cPair P Q → ∀ i' : Fin P, α (.inl i', .inr l) = 0) := by
  obtain ⟨_, _, F3, F4⟩ := monomial_facts P Q R S x μ f hf α hα
  have F5 := monomial_cols P Q R S x μ f hf α hα
  let A : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ i' : Fin P, (α (.inl i', .inl k) : ℚ)
    | .inr l => ∑ j' : Fin Q, (α (.inr j', .inr l) : ℚ)
  let B : Ix R S → ℚ := fun c => match c with
    | .inl k => ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)
    | .inr l => ∑ i' : Fin P, (α (.inl i', .inr l) : ℚ)
  have hA : ∀ c, 0 ≤ A c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hB : ∀ c, 0 ≤ B c := by
    rintro (k | l) <;> exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hν : ∀ c, A c - B c = shiftNu (cPair P Q) μ c := by
    rintro (k | l)
    · exact F3 k
    · exact F4 l
  have hsum : ∑ c, (A c + B c) = ∑ c, |A c - B c| := by
    simp only [hν]
    rw [show ∑ c, |shiftNu (cPair P Q) μ c| = degW (cPair P Q) μ from rfl, ← F5]
    rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [A, B, Fintype.sum_sum_type, Finset.sum_add_distrib]
    ring
  have hle : ∀ c ∈ Finset.univ, |A c - B c| ≤ A c + B c := fun c _ =>
    abs_le.2 ⟨by linarith [hA c, hB c], by linarith [hA c, hB c]⟩
  have hpure := (Finset.sum_eq_sum_iff_of_le hle).1 hsum.symm
  have hB0 : ∀ c, 0 ≤ A c - B c → B c = 0 := by
    intro c hc
    have := hpure c (Finset.mem_univ _)
    rw [abs_of_nonneg hc] at this
    linarith [hB c]
  constructor
  · intro k hk j'
    have h0 : B (.inl k) = 0 := hB0 (.inl k) (by have := hν (.inl k); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 j' (Finset.mem_univ _)
    exact_mod_cast this
  · intro l hl i'
    have h0 : B (.inr l) = 0 := hB0 (.inr l) (by have := hν (.inr l); simp only [shiftNu] at this; linarith)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.cast_nonneg _)).1 h0 i' (Finset.mem_univ _)
    exact_mod_cast this

theorem pderiv_eq_zero_of_coeff {σ : Type} [DecidableEq σ] (f : MvPolynomial σ ℂ) (v : σ)
    (h : ∀ α, coeff α f ≠ 0 → α v = 0) : pderiv v f = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  rw [mem_vars] at hv
  obtain ⟨α, hα, hαv⟩ := hv
  exact (Finsupp.mem_support_iff.1 hαv) (h α (mem_support_iff.1 hα))

theorem harm_shape_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) f →
    Q ≤ (j : ℕ) ∧ ∀ (j' : Fin Q) (k : Fin R), pderiv ((.inr j', .inl k) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) + (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) - (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (j' : Fin Q) (k : Fin R), α (.inr j', .inl k) = 0) ∧ Q ≤ (j : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> linarith)
    refine ⟨fun j' k => hw k j', ?_⟩
    by_contra hj
    push_neg at hj
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_add_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun j' k => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 j' k⟩

theorem harm_shape_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S)
    (f : Pol P Q R S), GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) f →
    P ≤ (i : ℕ) ∧ ∀ (i' : Fin P) (l : Fin S), pderiv ((.inl i', .inr l) : Ix P Q × Ix R S) f = 0 := by
  intro P Q P' Q' R S κ hN i j f hf
  obtain ⟨hα1, hβ1⟩ := alpha_beta_ge_one P Q P' Q' R S κ hN
  have hPR : P ≤ R := by rw [hN.1]; omega
  set μ := GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i) with hμ
  have hμl : ∀ k : Fin R, μ (.inl k) - cPair P Q =
      (if (k : ℕ) < P then (κ : ℚ) / 2 - cPair R S else 0) - (if k = i then 1 else 0) := by
    intro k
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inl.injEq, reduceCtorEq, if_false, add_zero]
    split_ifs <;> ring
  have hμr : ∀ l : Fin S, μ (.inr l) + cPair P Q =
      (if (l : ℕ) < Q then (κ : ℚ) / 2 + cPair R S else 0) + (if l = j then 1 else 0) := by
    intro l
    simp only [hμ, GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero]
    split_ifs <;> ring
  have key : ∀ α, coeff α f ≠ 0 → (∀ (i' : Fin P) (l : Fin S), α (.inl i', .inr l) = 0) ∧ P ≤ (i : ℕ) := by
    intro α hα0
    obtain ⟨cw, cu⟩ := col_pure P Q R S _ μ f hf α hα0
    have hu : ∀ (l : Fin S) (i' : Fin P), α (.inl i', .inr l) = 0 := fun l =>
      cu l (by rw [hμr]; split_ifs <;> linarith)
    refine ⟨fun i' l => hu l i', ?_⟩
    by_contra hi
    push_neg at hi
    have hw : ∀ (k : Fin R) (j' : Fin Q), α (.inr j', .inl k) = 0 := fun k =>
      cw k (by rw [hμl]; split_ifs <;> first | linarith | (subst_vars; omega))
    obtain ⟨F1, _, F3, _⟩ := monomial_facts P Q R S _ μ f hf α hα0
    have s1 : ∑ i' : Fin P, (∑ k : Fin R, (α (.inl i', .inl k) : ℚ) - ∑ l : Fin S, (α (.inl i', .inr l) : ℚ)) =
        P * ((κ : ℚ) / 2 - cPair R S) := by
      rw [Finset.sum_congr rfl (fun i' _ => F1 i')]; simp [mul_sub]
    have s3 : ∑ k : Fin R, (∑ i' : Fin P, (α (.inl i', .inl k) : ℚ) - ∑ j' : Fin Q, (α (.inr j', .inl k) : ℚ)) =
        ∑ k : Fin R, (μ (.inl k) - cPair P Q) := Finset.sum_congr rfl fun k _ => F3 k
    simp only [hu, hw, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at s1 s3
    rw [Finset.sum_congr rfl (fun k _ => hμl k), Finset.sum_sub_distrib, sum_fin_ite_lt P R hPR] at s3
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_zero, add_zero] at s3
    rw [Finset.sum_comm] at s3
    linarith
  obtain ⟨α, hα0⟩ := ne_zero_iff.1 hf.2.2.1
  exact ⟨(key α hα0).2, fun i' l => pderiv_eq_zero_of_coeff f _ fun β hβ => (key β hβ).1 i' l⟩

open GlobalTheory.RealLift in

theorem casK_addRoot_lr {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inl i) (.inr j)) = casK μ + 2 * (μ (.inl i) - μ (.inr j)) + 2 +
      ((R : ℚ) - 1 - 2 * (i : ℕ)) - ((S : ℚ) - 1 - 2 * (j : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub]
  have h1 : ∀ k : Fin R, (μ (.inl k) + if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then 2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) - if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then -2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

open GlobalTheory.RealLift in

theorem casK_addRoot_rl {R S : ℕ} (μ : Ix R S → ℚ) (i : Fin R) (j : Fin S) :
    casK (addRoot μ (.inr j) (.inl i)) = casK μ + 2 * (μ (.inr j) - μ (.inl i)) + 2 +
      ((S : ℚ) - 1 - 2 * (j : ℕ)) - ((R : ℚ) - 1 - 2 * (i : ℕ)) := by
  simp only [casK, addRoot, Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, sub_zero, add_zero, zero_sub, zero_add]
  have h1 : ∀ k : Fin R, (μ (.inl k) - if k = i then 1 else 0) ^ 2 = μ (.inl k) ^ 2 + (if k = i then -2 * μ (.inl i) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  have h2 : ∀ k : Fin S, (μ (.inr k) + if k = j then 1 else 0) ^ 2 = μ (.inr k) ^ 2 + (if k = j then 2 * μ (.inr j) + 1 else 0) := by
    intro k; split_ifs with h <;> [subst h; skip] <;> ring
  simp only [h1, h2, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem casK_lt_inl_inr : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (i : ℕ) < P → Q ≤ (j : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inl i) (.inr j)) := by
  intro P Q P' Q' R S κ hN i j hi hj
  rw [casK_addRoot_lr]
  have hj' : ¬ (j : ℕ) < Q := not_lt.2 hj
  simp only [GlobalTheory.RealLift.lam, hi, hj', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hi' : ((i : ℕ) : ℚ) + 1 ≤ P := by exact_mod_cast hi
  have hj'' : (Q : ℚ) ≤ ((j : ℕ) : ℚ) := by exact_mod_cast hj
  push_cast
  linarith

theorem casK_lt_inr_inl : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ (i : Fin R) (j : Fin S),
    (j : ℕ) < Q → P ≤ (i : ℕ) → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) <
      GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) (.inr j) (.inl i)) := by
  intro P Q P' Q' R S κ hN i j hj hi
  rw [casK_addRoot_rl]
  have hi' : ¬ (i : ℕ) < P := not_lt.2 hi
  simp only [GlobalTheory.RealLift.lam, hj, hi', if_true, if_false, cPair]
  have hk : ((R + S : ℕ) : ℤ) < κ := hN.2.2.2.2.2.2
  have hk' : ((R : ℚ) + S) < (κ : ℚ) := by exact_mod_cast hk
  have hj'' : ((j : ℕ) : ℚ) + 1 ≤ Q := by exact_mod_cast hj
  have hi'' : (P : ℚ) ≤ ((i : ℕ) : ℚ) := by exact_mod_cast hi
  push_cast
  linarith

theorem _root_.GlobalTheory.RealLift.casK_lt_of_isHarmVec_addRoot : ∀ (P Q P' Q' R S : ℕ) (κ : ℤ), GlobalTheory.RealLift.Num P Q P' Q' R S κ → ∀ a b : Formalism.BasicNotions.TH.Ix R S, ¬ Formalism.BasicNotions.TH.sameBlock a b → ∀ f : Formalism.BasicNotions.TH.Pol P Q R S, GlobalTheory.RealLift.IsHarmVec ((κ : ℚ) / 2) (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) f → GlobalTheory.RealLift.casK (GlobalTheory.RealLift.lam P Q R S κ) + ((R + S : ℕ) : ℚ) < GlobalTheory.RealLift.casK (GlobalTheory.RealLift.addRoot (GlobalTheory.RealLift.lam P Q R S κ) a b) := by
  intro P Q P' Q' R S κ hN a b hab f hf
  rcases a with i | j <;> rcases b with i' | j'
  · exact absurd trivial hab
  · obtain ⟨hj, hw⟩ := harm_shape_inl_inr P Q P' Q' R S κ hN i j' f hf
    have hi : (i : ℕ) < P := by
      by_contra h
      exact not_hw_of_wFree P Q R S _ i f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]) hw hf.2.2
    exact casK_lt_inl_inr P Q P' Q' R S κ hN i j' hi hj
  · obtain ⟨hi, hu⟩ := harm_shape_inr_inl P Q P' Q' R S κ hN i' j f hf
    have hj : (j : ℕ) < Q := by
      by_contra h
      exact not_hw_of_uFree P Q R S _ j f (not_lt.1 h) (by simp [GlobalTheory.RealLift.addRoot, GlobalTheory.RealLift.lam, h]; ring) hu hf.2.2
    exact casK_lt_inr_inl P Q P' Q' R S κ hN i' j hj hi
  · exact absurd trivial hab

end GlobalTheory.RealLift.SteepHarm

end
