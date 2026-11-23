import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount.IdemCen

variable (D : D7)

local instance neZeroTypePrime (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def fac (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :=
  if h : kv.1 = k then h.symm ▸ D.ntypes.eSer k (t (h ▸ kv.2)) else 1

variable {D}

theorem fac_self (k : Fin 2) (t : Tup D k) (v : D.nd.PlG k) : fac D k t ⟨k, v⟩ = D.ntypes.eSer k (t v) := by
  simp [fac]

theorem fac_ne (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (h : kv.1 ≠ k) : fac D k t kv = 1 := by
  simp [fac, h]

open Classical in

theorem prod_fac_coeff (k : Fin 2) (t : Tup D k) (g : G0g D.nd) :
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (fac D k t kv).coeff (g kv) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
        ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  rw [Fintype.prod_sigma, Fintype.prod_eq_mul_prod_compl k]
  simp only [fac_self]
  have h2 : ∏ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then 1 else 0 := by
    have e : ∀ k' ∈ ({k}ᶜ : Finset (Fin 2)), ∏ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) =
        if ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1 then 1 else 0 := by
      intro k' hk'
      have hk : k' ≠ k := by simpa using hk'
      have hv : ∀ v : D.nd.PlG k', (fac D k t ⟨k', v⟩).coeff (g ⟨k', v⟩) = if g ⟨k', v⟩ = 1 then 1 else 0 := by
        intro v
        rw [fac_ne k t ⟨k', v⟩ hk, MonoidAlgebra.one_def, MonoidAlgebra.coeff_single_apply]
        by_cases hg : g ⟨k', v⟩ = 1
        · rw [if_pos hg.symm, if_pos hg]
        · rw [if_neg (Ne.symm hg), if_neg hg]
      simp only [hv]
      by_cases hc : ∀ v : D.nd.PlG k', g ⟨k', v⟩ = 1
      · rw [if_pos hc]
        exact Finset.prod_eq_one fun v _ => if_pos (hc v)
      · rw [if_neg hc]
        push_neg at hc
        obtain ⟨v, hv'⟩ := hc
        exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv')
    rw [Finset.prod_congr rfl e, Finset.prod_boole]
    by_cases hc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1
    · rw [if_pos hc, if_pos]
      intro k' hk' v
      exact hc ⟨k', v⟩ (by simpa using hk')
    · rw [if_neg hc, if_neg]
      intro h
      apply hc
      rintro ⟨k', v⟩ hk
      exact h k' (by simpa using hk) v
  rw [h2]
  split_ifs <;> simp

theorem badElt_eq_sum (k : Fin 2) (S : Finset (Tup D k)) :
    badElt D k S = ∑ t ∈ S, Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) := by
  apply MonoidAlgebra.coeff_injective
  ext g
  rw [MonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  simp only [Formalism.BasicNotions.Examples₂.NZ.tens_coeff, prod_fac_coeff]
  simp only [badElt, MonoidAlgebra.coeff_ofCoeff, Finsupp.equivFunOnFinite_symm_apply_apply]
  split_ifs with hc
  · rfl
  · simp

theorem fac_mul_self (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) :
    fac D k t kv * fac D k t kv = fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_idem]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul]

theorem fac_central (k : Fin 2) (t : Tup D k) (kv : Σ k : Fin 2, D.nd.PlG k) (a) :
    fac D k t kv * a = a * fac D k t kv := by
  rcases kv with ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    rw [fac_self, D.ntypes.eSer_central]
  · rw [fac_ne k t ⟨k', v⟩ h, one_mul, mul_one]

theorem tens_fac_mul_of_ne (k : Fin 2) {t t' : Tup D k} (h : t ≠ t') :
    Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t) * Formalism.BasicNotions.Examples₂.NZ.tens (fac D k t') = 0 := by
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  rw [Formalism.BasicNotions.Examples₂.NZ.tens_mul]
  refine Formalism.BasicNotions.Examples₂.NZ.tens_eq_zero _ ⟨k, v⟩ ?_
  simp only [fac_self]
  exact D.ntypes.eSer_orth k _ _ hv

theorem badElt_idem_central : ∀ (D : D7) (k : Fin 2) (S : Finset (Tup D k)),
    badElt D k S * badElt D k S = badElt D k S ∧ ∀ a, badElt D k S * a = a * badElt D k S := by
  intro D k S
  rw [badElt_eq_sum]
  refine ⟨?_, fun a => ?_⟩
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.sum_eq_single_of_mem t ht fun t' _ hne => tens_fac_mul_of_ne k (Ne.symm hne),
      Formalism.BasicNotions.Examples₂.NZ.tens_mul]
    exact congrArg _ (funext fun kv => fac_mul_self k t kv)
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ =>
      Formalism.BasicNotions.Examples₂.NZ.tens_central _ (fun kv b => fac_central k t kv b) a

end GlobalTheory.BadCount.IdemCen
