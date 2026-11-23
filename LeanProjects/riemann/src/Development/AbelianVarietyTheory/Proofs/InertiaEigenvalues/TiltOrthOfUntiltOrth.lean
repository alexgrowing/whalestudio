import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltSumSubLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem tilt_orth_of_untilt_orth : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (m : Fin h → Fl l), (∀ i j, ‖sh (m i)‖ < l * ‖sh (m j)‖) →
    (∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖sh (m j)‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * sh (m i)‖) →
    ∀ (c : Fin h → ℤ) (j : Fin h), ¬ (l : ℤ) ∣ c j → ‖sh (m j)‖ ≤ ‖sh (∑ i, (c i : Fl l) * m i)‖ := by
  intro l _ h m hrat horth c j hj
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (0 : ℤ) < l := by exact_mod_cast (Fact.out : l.Prime).pos

  have hne : (Finset.univ : Finset (Fin h)).Nonempty := ⟨j, Finset.mem_univ _⟩
  set M : ℝ := Finset.univ.sup' hne (fun i => ‖sh (m i)‖) with hM
  have hMle : ∀ i, ‖sh (m i)‖ ≤ M := fun i => Finset.le_sup' (fun i => ‖sh (m i)‖) (Finset.mem_univ i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMle j)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖sh (m i)‖)
  have hsmall : ‖(l : ℂ_[l])‖ * M < ‖sh (m j)‖ := by
    rw [GlobalTheory.PSer.Laws.norm_l, hM, hi0, inv_mul_lt_iff₀ hl]
    exact hrat i0 j

  set n : Fin h → ℕ := fun i => (c i % (l : ℤ)).toNat with hn
  have hnc : ∀ i, ((n i : ℕ) : ℤ) = c i % (l : ℤ) := fun i =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hl0.ne')
  have hcast : ∀ i, (c i : Fl l) = (n i : Fl l) := by
    intro i
    have : ((n i : ℤ) : Fl l) = (n i : Fl l) := Int.cast_natCast _
    rw [← this, CharP.intCast_eq_intCast (Fl l) l, hnc]
    exact (Int.mod_modEq _ _).symm
  have hnj : ‖((n j : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
    intro hd
    apply hj
    have h1 : (l : ℤ) ∣ c j % (l : ℤ) := by rw [← hnc]; exact_mod_cast hd
    have h2 := (Int.dvd_iff_emod_eq_zero ..).1 h1
    rw [Int.emod_emod_of_dvd _ (dvd_refl _)] at h2
    exact Int.dvd_of_emod_eq_zero h2

  have hsum : (∑ i, (c i : Fl l) * m i) =
      ∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), m p.1 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcast]
  have hsum2 : (∑ p ∈ (Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)), sh (m p.1)) =
      ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, map_natCast]
  obtain ⟨hd, -⟩ := GlobalTheory.T.norm_sh_sum_sub_sum_sh_le l ((_ : Fin h) × ℕ) ((Finset.univ : Finset (Fin h)).sigma (fun i => Finset.range (n i)))
    M (fun p => m p.1) hM0 (fun p _ => hMle p.1)
  rw [← hsum, hsum2] at hd
  have ho := horth (fun i => ((n i : ℕ) : ℚ_[l])) j
  simp only [hnj, one_mul] at ho

  by_contra hlt
  push_neg at hlt
  set b := sh (∑ i, (c i : Fl l) * m i)
  set a := ∑ i, algebraMap ℚ_[l] ℂ_[l] ((n i : ℕ) : ℚ_[l]) * sh (m i)
  have : ‖a‖ ≤ max ‖b‖ ‖b - a‖ := by
    have := IsUltrametricDist.norm_add_le_max b (-(b - a))
    rwa [norm_neg, show b + -(b - a) = a by ring] at this
  have hba : ‖b - a‖ < ‖sh (m j)‖ := hd.trans_lt hsmall
  exact absurd (ho.trans this) (not_le.2 (max_lt hlt hba))

end GlobalTheory
