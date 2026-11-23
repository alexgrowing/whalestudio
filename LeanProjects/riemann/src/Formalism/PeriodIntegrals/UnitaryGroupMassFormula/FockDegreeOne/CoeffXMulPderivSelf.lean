import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.FockOperatorsKernel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.RedDefs

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW.HwC

def sgnL {p q r s : ℕ} (l : Ln p q r s) : ℚ := if linePos l = true then 1 else -1

def wtv {p q r s : ℕ} (β : Ln p q r s →₀ ℕ) (c : Ix p q) : ℚ :=
  ∑ d : Ix r s, sgnL ((c, d) : Ln p q r s) * (β (c, d) : ℚ) + kShift r s c

theorem coeff_X_mul_pderiv_self {σ : Type*} (l : σ) (P : MvPolynomial σ ℂ) (β : σ →₀ ℕ) :
    coeff β (X l * pderiv l P) = (β l : ℂ) * coeff β P := by
  classical
  rw [coeff_X_mul']
  by_cases h : l ∈ β.support
  · rw [if_pos h, coeff_pderiv]
    have h1 : 1 ≤ β l := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp h)
    have hle : Finsupp.single l 1 ≤ β := Finsupp.single_le_iff.mpr h1
    rw [tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same, mul_comm]
    congr 1
    rw [Nat.cast_sub h1]
    push_cast
    ring
  · rw [if_neg h]
    have h0 : β l = 0 := by simpa [Finsupp.mem_support_iff] using h
    simp [h0]

theorem coeff_X_mul_pderiv_ne {σ : Type*} (l l' : σ) (P : MvPolynomial σ ℂ) (γ : σ →₀ ℕ)
    (h : coeff γ (X l * pderiv l' P) ≠ 0) :
    ∃ β ∈ P.support, β + Finsupp.single l 1 = γ + Finsupp.single l' 1 := by
  classical
  rw [coeff_X_mul'] at h
  by_cases hs : l ∈ γ.support
  · rw [if_pos hs, coeff_pderiv] at h
    refine ⟨γ - Finsupp.single l 1 + Finsupp.single l' 1, ?_, ?_⟩
    · rw [mem_support_iff]
      exact left_ne_zero_of_mul h
    · have hle : Finsupp.single l 1 ≤ γ :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs))
      rw [add_right_comm, tsub_add_cancel_of_le hle]
  · rw [if_neg hs] at h
    exact absurd rfl h

theorem wtv_add {p q r s : ℕ} (β γ : Ln p q r s →₀ ℕ) (c : Ix p q) :
    wtv (β + γ) c = wtv β c + wtv γ c - kShift r s c := by
  unfold wtv
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  ring

theorem wtv_single {p q r s : ℕ} (l : Ln p q r s) (c : Ix p q) :
    wtv (Finsupp.single l 1) c = (if l.1 = c then sgnL l else 0) + kShift r s c := by
  unfold wtv
  congr 1
  have key : ∀ d : Ix r s, sgnL ((c, d) : Ln p q r s) * ((Finsupp.single l 1 ((c, d) : Ln p q r s) : ℕ) : ℚ) =
      if d = l.2 ∧ l.1 = c then sgnL l else 0 := by
    intro d
    by_cases h1 : d = l.2 ∧ l.1 = c
    · obtain ⟨rfl, rfl⟩ := h1
      simp
    · rw [if_neg h1]
      have hne : l ≠ ((c, d) : Ln p q r s) := fun he => h1 ⟨by rw [he], by rw [he]⟩
      simp [Finsupp.single_apply, hne]
  simp_rw [key]
  by_cases h : l.1 = c <;> simp [h]

theorem wtv_shift {p q r s : ℕ} (l l' : Ln p q r s) (β γ : Ln p q r s →₀ ℕ)
    (h : β + Finsupp.single l 1 = γ + Finsupp.single l' 1) (c : Ix p q) :
    wtv γ c = wtv β c + (if l.1 = c then sgnL l else 0) - (if l'.1 = c then sgnL l' else 0) := by
  have h1 := wtv_add β (Finsupp.single l 1) c
  have h2 := wtv_add γ (Finsupp.single l' 1) c
  rw [h] at h1
  rw [h2, wtv_single, wtv_single] at h1
  linarith

theorem sameBlock_refl' {p q : ℕ} (c : Ix p q) : sameBlock c c := by
  cases c <;> trivial

theorem coeff_Ecc {p q r s : ℕ} (c : Ix p q) (P : Pol p q r s) (β : Ln p q r s →₀ ℕ) :
    coeff β (fockAct1 p q r s (Eab c c) P) = ((wtv β c : ℚ) : ℂ) * coeff β P := by
  classical
  have hline : ∀ l : Ln p q r s, coeff β (omE l l P) =
      (((sgnL l * β l + sgnL l / 2 : ℚ)) : ℂ) * coeff β P := by
    intro l
    by_cases hl : linePos l = true
    · simp only [omE, raiB, lowB, hl, if_true, LinearMap.add_apply, Module.End.mul_apply,
        LinearMap.mulLeft_apply, Derivation.coeFn_coe, LinearMap.smul_apply,
        Module.End.one_apply, coeff_add, coeff_smul, smul_eq_mul, coeff_X_mul_pderiv_self, sgnL]
      push_cast
      ring
    · have hl' : linePos l = false := by simpa using hl
      have e : coeff β (pderiv l (X l * P)) = ((β l : ℂ) + 1) * coeff β P := by
        rw [coeff_pderiv, add_comm β, coeff_X_mul, mul_comm]
      simp only [omE, raiB, lowB, hl', Bool.false_eq_true, if_false, if_true, LinearMap.add_apply,
        Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.neg_apply, Derivation.coeFn_coe,
        LinearMap.smul_apply, Module.End.one_apply, coeff_add, coeff_neg, coeff_smul, smul_eq_mul, e, sgnL]
      push_cast
      ring
  rw [fockAct1_Eab_apply, coeff_sum]
  simp_rw [hline]
  rw [← Finset.sum_mul]
  congr 1
  unfold wtv
  push_cast
  rw [Finset.sum_add_distrib]
  congr 1
  cases c with
  | inl i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring
  | inr i => simp [kShift, cPair, sgnL, linePos, Fintype.sum_sum_type]; ring

theorem wt_Eab {p q r s : ℕ} (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b)
    (P : Pol p q r s) (γ : Ln p q r s →₀ ℕ) (hγ : γ ∈ (fockAct1 p q r s (Eab a b) P).support) :
    ∃ β ∈ P.support, ∀ c, wtv γ c =
      wtv β c + (if a = c then 1 else 0) - (if b = c then 1 else 0) := by
  classical
  rw [fockAct1_Eab_apply, mem_support_iff, coeff_sum] at hγ
  obtain ⟨d, -, hd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hγ
  have hne' : ((a, d) : Ln p q r s) ≠ (b, d) := fun h => hne (Prod.ext_iff.mp h).1
  have hpos : linePos ((a, d) : Ln p q r s) = linePos ((b, d) : Ln p q r s) := by
    cases a <;> cases b <;> cases d <;> simp_all [sameBlock, linePos]
  simp only [omE, if_neg hne', add_zero, Module.End.mul_apply] at hd
  by_cases hl : linePos ((a, d) : Ln p q r s) = true
  · have hl2 : linePos ((b, d) : Ln p q r s) = true := hpos ▸ hl
    simp only [raiB, lowB, hl, hl2, if_true, LinearMap.mulLeft_apply,
      Derivation.coeFn_coe] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl, hl2]
  · have hl1 : linePos ((a, d) : Ln p q r s) = false := by simpa using hl
    have hl2 : linePos ((b, d) : Ln p q r s) = false := hpos ▸ hl1
    have e : pderiv ((a, d) : Ln p q r s) (X ((b, d) : Ln p q r s) * P) =
        X ((b, d) : Ln p q r s) * pderiv ((a, d) : Ln p q r s) P := by
      rw [Derivation.leibniz, pderiv_X, Pi.single_apply, if_neg hne'.symm]
      simp [mul_comm]
    simp only [raiB, lowB, hl1, hl2, Bool.false_eq_true, if_false, LinearMap.mulLeft_apply,
      LinearMap.neg_apply, Derivation.coeFn_coe, e, coeff_neg, ne_eq, neg_eq_zero] at hd
    obtain ⟨β, hβ, hsum⟩ := coeff_X_mul_pderiv_ne _ _ P γ hd
    refine ⟨β, hβ, fun c => ?_⟩
    rw [wtv_shift _ _ β γ hsum c]
    simp [sgnL, hl1, hl2]
    split_ifs <;> ring

def IsWt {p q r s : ℕ} (ν : Ix p q → ℚ) (P : Pol p q r s) : Prop :=
  ∀ β ∈ P.support, ∀ c, wtv β c = ν c

theorem Ecc_of_wt {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P) (c : Ix p q) :
    fockAct1 p q r s (Eab c c) P = ((ν c : ℚ) : ℂ) • P := by
  ext β
  rw [coeff_Ecc, coeff_smul, smul_eq_mul]
  by_cases hβ : β ∈ P.support
  · rw [hP β hβ c]
  · have h0 : coeff β P = 0 := by simpa [mem_support_iff] using hβ
    rw [h0, mul_zero, mul_zero]

theorem wt_Eab_of {p q r s : ℕ} {ν : Ix p q → ℚ} {P : Pol p q r s} (hP : IsWt ν P)
    (a b : Ix p q) (hab : sameBlock a b) (hne : a ≠ b) :
    IsWt (fun c => ν c + (if a = c then 1 else 0) - (if b = c then 1 else 0))
      (fockAct1 p q r s (Eab a b) P) := by
  intro γ hγ c
  obtain ⟨β, hβ, h⟩ := wt_Eab a b hab hne P γ hγ
  rw [h c, hP β hβ c]

end PI.FockOneDegW.HwC
