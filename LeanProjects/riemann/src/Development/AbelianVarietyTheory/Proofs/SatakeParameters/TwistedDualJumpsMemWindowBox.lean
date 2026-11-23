import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordJumpsInWindowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordSmallJumpsCardStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem sum_count_Icc (s : Multiset ℤ) (η : ℕ) :
    ∑ u ∈ Finset.Icc (-(η : ℤ)) η, ((s.count u : ℕ) : ℤ) =
      ((s.filter fun u : ℤ => |u| ≤ (η : ℤ)).card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    by_cases hx : |x| ≤ (η : ℤ)
    · have hm : x ∈ Finset.Icc (-(η : ℤ)) η := Finset.mem_Icc.2 (abs_le.1 hx)
      rw [Multiset.filter_cons_of_pos (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, Multiset.card_cons, ← Finset.add_sum_erase _ _ hm,
        Multiset.count_cons_self]
      have he : ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u (x ::ₘ s) : ℕ) : ℤ) =
          ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u s : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun u hu => by
          rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hu)]
      rw [he]
      push_cast
      rw [← ih, ← Finset.add_sum_erase _ _ hm]
      ring
    · have hm : x ∉ Finset.Icc (-(η : ℤ)) η := fun h => hx (abs_le.2 (Finset.mem_Icc.1 h))
      rw [Multiset.filter_cons_of_neg (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, ← ih]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Multiset.count_cons_of_ne (fun h => hm (by rw [← h]; exact hu))]

theorem letter_one_zero {φ : Formalism.HC.Frame} (τ : φ.GG) : letter τ 1 (0 : ZMod (orderOf (1 : φ.GG))) = τ := by
  simp [letter]

theorem recWord_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  intro D L C j ε n g hR a
  obtain ⟨hT1, hbox⟩ := GlobalTheory.T.twistedDualPageWord_jumps_in_windows L C j ε (g a) 1 hR
  obtain ⟨hT2, hcard⟩ := GlobalTheory.T.pageWord_T2_and_J2_card_of_roomy L C j ε (g a) 1 hR
  obtain ⟨hsz, hMi, hhi, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g a) 1 hR 0
  have hl := letter_one_zero (g a)
  have t1 := hT1 0
  have t2 := hT2 0
  have bx := hbox 0
  have cd := (hcard 0).2
  simp only [pageWord, recWord, WordData.Mi, WordData.hi, hl] at t1 t2 bx cd hsz hMi hhi
  refine ⟨fun u hu => ?_, fun u hu => (t2.1 u hu), ?_⟩
  · have h1 := t1 u hu
    have h2 := bx u hu
    refine ⟨?_, ?_⟩
    · simp only [NWord.win, recWord, Set.mem_setOf_eq]
      rw [hsz]
      exact h1
    · simp only [recWord, Set.mem_Icc]
      rw [hMi, hhi]
      exact h2
  · rw [sum_count_Icc, cd]

end GlobalTheory.HTW.Rec
