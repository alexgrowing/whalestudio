import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedCardG
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedGcd

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem xsOf_filter (L : PeriodPair) (α β : ℂ) (hα : MulStable L α) (hβ : MulStable L β) (T T' : Finset ℂ)
    (hT : IsHalfReps L α T) (hT' : IsHalfReps L β T') :
    xsOf L (T.filter (fun P => β * P ∈ L.lattice)) = xsOf L T ∩ xsOf L T' := by
  ext x
  simp only [xsOf, Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨P, ⟨hP, hβP⟩, rfl⟩
    refine ⟨⟨P, hP, rfl⟩, ?_⟩
    have := (hT'.mem_xsOf hβ (hT.notMem hP)).2 hβP
    simpa only [xsOf, Finset.mem_image] using this
  · rintro ⟨⟨P, hP, rfl⟩, h2⟩
    refine ⟨P, ⟨hP, ?_⟩, rfl⟩
    refine (hT'.mem_xsOf hβ (hT.notMem hP)).1 ?_
    simpa only [xsOf, Finset.mem_image] using h2

theorem natCast_mulStable (L : PeriodPair) (n : ℕ) : MulStable L (n : ℂ) := by
  intro ω hω
  have := L.lattice.nsmul_mem hω n
  simpa [nsmul_eq_mul] using this

theorem kerProd_ideal (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L)
    (l : ℕ) (hl : l.Prime) (h3 : 3 ∣ d) (hd3 : d ≠ 3) : KerProdAt d L l 3 := by
  obtain ⟨p, r, hp, hb, -, hp3, hr, hdiv, hndiv⟩ := prime_choice d (l + 3) hsq hd4 h3 hd3
  obtain ⟨M, hM⟩ := hdiv
  have hpM : ¬ p ∣ M := by
    rintro ⟨c, rfl⟩
    exact hndiv ⟨c, by rw [hM]; ring⟩
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set β : ℂ := (r : ℂ) + redSqD d with hβdef
  have hβs : MulStable L β := sqD_mulStable d L hCM r
  have hβN : Complex.normSq β = ((p * M : ℕ) : ℝ) := by rw [← hM]; exact sqD_normSq d r
  have hβN' : Complex.normSq β = ((r ^ 2 + d : ℕ) : ℝ) := sqD_normSq d r
  have hps : MulStable L (p : ℂ) := natCast_mulStable L p
  have hpN : Complex.normSq (p : ℂ) = ((p * p : ℕ) : ℝ) := by
    rw [Complex.normSq_natCast]; push_cast; ring
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hdodd : Odd d := by rw [Nat.odd_iff]; omega
  have hNodd : Odd (r ^ 2 + d) := (hr.pow_of_ne_zero two_ne_zero).add_odd hdodd
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hβN'
    have : (r ^ 2 + d : ℕ) = 0 := by exact_mod_cast hβN'.symm
    omega
  obtain ⟨T, hT⟩ := halfReps_exist L (p : ℂ) hp0 hps (p * p) hpN (hpodd.mul hpodd)
  obtain ⟨T', hT'⟩ := halfReps_exist L β hβ0 hβs (r ^ 2 + d) hβN' hNodd
  have hcard := card_G L β hβs p M hp hp2 hβN hpM T hT
  refine ⟨p, T.filter (fun P => β * P ∈ L.lattice), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rcases (Nat.dvd_prime hp).1 h with h1 | h1
    · exact hl.one_lt.ne' h1
    · omega
  · omega
  · omega
  · intro z hz
    have hz' := (Finset.mem_filter.1 hz).1
    exact ⟨hT.notMem hz', (hT.1 z hz').1⟩
  · intro k h2 h3' hω
    have hpk : (p : ℂ) ∈ k := natCast_mem k p
    have hβk : β ∈ k := by
      rw [hβdef, redSqD]
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by simp) hω) k.one_mem)
    have h1 := kerPoly_mem L (p : ℂ) T hp0 hps hT k h2 h3' hpk
    have h1' := kerPoly_mem L β T' hβ0 hβs hT' k h2 h3' hβk
    have h4 := prod_mem_of_rootPoly k _ (rootPoly_inter_mem k _ _ h1 h1')
    rw [← xsOf_filter L (p : ℂ) β hps hβs T T' hT hT', xsOf, Finset.prod_image] at h4
    · exact h4
    · intro a ha b hb hab
      exact hT.injOn (Finset.mem_coe.2 (Finset.mem_filter.1 ha).1)
        (Finset.mem_coe.2 (Finset.mem_filter.1 hb).1) hab

end ReciprocityTheory.ChartRestriction.L1
