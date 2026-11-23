import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PSer

theorem emod_toNat_lt (h : ℕ) (hh : 1 ≤ h) (k : ℤ) : (k % (h : ℤ)).toNat < h := by
  have h0 : (0 : ℤ) < h := by exact_mod_cast hh
  have := Int.emod_lt_of_pos k h0
  have := Int.emod_nonneg k h0.ne'
  omega

def reCoef (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) : ℂ_[l] :=
  (l : ℂ_[l]) ^ (-(k / (h : ℤ))) * μ ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩

theorem reCoef_add (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) :
    reCoef l h hh μ k = (l : ℂ_[l]) * reCoef l h hh μ (k + h) := by
  have hl : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have e1 : (k + h) / (h : ℤ) = k / h + 1 := by
    have := Int.add_mul_ediv_right k 1 h0; simpa using this
  have e2 : (k + h) % (h : ℤ) = k % h := by simp
  unfold reCoef
  simp only [e1, e2]
  rw [neg_add, zpow_add₀ hl, zpow_neg_one]
  field_simp

theorem reCoef_at (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (n : ℤ) (i : Fin h) :
    reCoef l h hh μ (n * h + i) = (l : ℂ_[l]) ^ (-n) * μ i := by
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have hih : (i : ℤ) < h := by exact_mod_cast i.isLt
  have e1 : (n * h + i) / (h : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ h0, Int.ediv_eq_zero_of_lt hi0 hih, zero_add]
  have e2 : (n * h + i) % (h : ℤ) = i := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]
  unfold reCoef
  congr 2
  · rw [e1]
  · ext; simp [e2]

theorem emod_at (h : ℕ) (hh : 1 ≤ h) (n : ℤ) (i : Fin h) :
    (n * h + ((i : ℕ) : ℤ)) % (h : ℤ) = ((i : ℕ) : ℤ) := by
  have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
  have hih : ((i : ℕ) : ℤ) < h := by exact_mod_cast i.isLt
  rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]

theorem exists_coef_hasSum_lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 →
    ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧
      ∀ x : Fl l, ‖sh x‖ < 1 →
        HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  intro l _ h μ hh hμ
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  refine ⟨reCoef l h hh μ, reCoef_add l h hh μ, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra H; push_neg at H; exact hμ (funext H)
    refine ⟨((i : ℕ) : ℤ), ?_⟩
    have := reCoef_at l h hh μ 0 i
    simp only [zero_mul, zero_add, neg_zero, zpow_zero, one_mul] at this
    rw [this]; exact hi
  · intro x hx
    let f : ℤ → ℂ_[l] := fun k => reCoef l h hh μ k * sh (pw k x)
    let F : Fin h → ℤ → ℂ_[l] := fun i k => if k % (h : ℤ) = ((i : ℕ) : ℤ) then f k else 0
    have hF : ∀ k, f k = ∑ i, F i k := by
      intro k
      have hn : 0 ≤ k % (h : ℤ) := Int.emod_nonneg k h0
      rw [Finset.sum_eq_single ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩]
      · simp only [F]; rw [if_pos (by simp [Int.toNat_of_nonneg hn])]
      · intro b _ hb
        simp only [F]
        rw [if_neg]
        intro hbk
        apply hb
        ext
        simp only
        omega
      · intro hc; exact absurd (Finset.mem_univ _) hc
    have hFi : ∀ i : Fin h, HasSum (F i) (μ i * lam h i x) := by
      intro i
      have hg : Function.Injective (fun n : ℤ => n * h + ((i : ℕ) : ℤ)) := by
        intro a b e
        have e' : a * (h : ℤ) = b * h := by simpa using e
        exact mul_right_cancel₀ h0 e'
      rw [← hg.hasSum_iff]
      · have := ((GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h i ‖sh x‖ x hh hx le_rfl).1).mul_left (μ i)
        have heq : (F i ∘ fun n : ℤ => n * h + ((i : ℕ) : ℤ)) =
            fun n : ℤ => μ i * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((i : ℕ) : ℤ)) x)) := by
          funext n
          simp only [Function.comp, F, f]
          rw [if_pos (emod_at h hh n i), reCoef_at]
          ring
        rw [heq]; exact this
      · intro k hk
        simp only [F]
        rw [if_neg]
        intro hki
        apply hk
        refine ⟨k / h, ?_⟩
        have := Int.ediv_mul_add_emod k (h : ℤ)
        simp only
        rw [← hki]
        linarith [mul_comm (k / (h : ℤ)) (h : ℤ)]
    have := hasSum_sum (s := Finset.univ) (fun i _ => hFi i)
    have hf : f = fun k => ∑ i, F i k := funext hF
    show HasSum f _
    rw [hf]; exact this

end GlobalTheory.PSer
end
