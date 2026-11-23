import Mathlib
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

theorem exists_sel (X : Fields) : ∃ sel, IsSel X sel := by
  classical
  have h : ∀ v : HeightOneSpectrum (𝓞 X.F), ∃ P : HeightOneSpectrum (𝓞 X.E),
      P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
    intro v
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
    have hQ0 : Q ≠ ⊥ := by
      intro h0
      apply v.ne_bot
      rw [hQ.over, h0, Ideal.under_bot]
    exact ⟨⟨Q, hQm.isPrime, hQ0⟩, hQ.over.symm⟩
  choose sel hsel using h
  exact ⟨sel, hsel⟩

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dif_pos (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

theorem resChar_QE_ne (hX : X.Ok) (hsel : IsSel X sel) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    resChar (mu : Chr X.F X.E X.K) P ≠ 1 := by
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp hP
  obtain ⟨⟨P1, P2, hne, hsp⟩, -, -⟩ := mu.good hv
  have hm := (mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2
  have hR := residue_character_ramified X.F X.E X.K hX.rankE (mu : Chr X.F X.E X.K) hm.2.2.1 hm.2.1
  by_cases h1 : sel v = P1
  · rw [h1]; exact (hR v P1 P2 hne hsp).mp hv
  · by_cases h2 : sel v = P2
    · rw [h2]; exact (hR v P2 P1 hne.symm (by rw [hsp, mul_comm])).mp hv
    · exact absurd (hsel v) (d_other hsp h1 h2)

theorem rowTyQ_ne (R : Ranks) (hX : X.Ok) (hsel : IsSel X sel) (P : QE sel (mu : Chr X.F X.E X.K)) :
    (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) P).lam ≠ 1 ∧
    (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) P).lam ≠ 1 := by
  have ht : 0 < R.t := by have := R.rank_add_five_le; omega
  have hm : 0 < R.m := by have := R.two_le_m; omega
  constructor
  · intro h
    exact lamQ_ne_one (Nat.mul_pos hm ht) (le_of_eq (rank_X'_eq R).symm) (resChar_QE_ne mu hX hsel P.1 P.2) (inv_eq_one.mp h)
  · exact lamQ_ne_one ht le_rfl (resChar_QE_ne mu hX hsel P.1 P.2)

theorem qdat_tied (hsel : IsSel X sel) :
    QDat.TiedTo (⟨QE sel (mu : Chr X.F X.E X.K), fun P => resChar (mu : Chr X.F X.E X.K) P.1⟩ : QDat X) (mu : Chr X.F X.E X.K) where
  places := by
    intro v
    constructor
    · intro hv
      exact ⟨sel v, (mem_QE sel mu _).mpr ⟨v, hv, rfl⟩, hsel v⟩
    · rintro ⟨P, hP, e⟩
      obtain ⟨v', hv', rfl⟩ := (mem_QE sel mu P).mp hP
      have : v' = v := HeightOneSpectrum.ext ((hsel v').symm.trans e)
      exact this ▸ hv'
  res := fun _ => rfl

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

open Classical in

theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
