import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.Jumps

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem map_round_cast (S : Multiset ℂ) (h : ∀ z ∈ S, ∃ n : ℤ, z = (n : ℂ)) :
    (S.map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S := by
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id S]
  refine Multiset.map_congr rfl fun z hz => ?_
  obtain ⟨n, rfl⟩ := h z hz
  simp

theorem exists_jumpsAre_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J := by
  classical
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩
  let S : (D.host.E →+* ℂ) → Multiset ℂ := fun τc =>
    (D.naut.infG π τc).map fun z => -z - ((((1 - (D.R.t : ℝ)) / 2 : ℝ)) : ℂ)
  have hint : ∀ τc, ∀ w ∈ S τc, ∃ n : ℤ, w = (n : ℂ) := by
    intro τc w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hw
    obtain ⟨n, rfl⟩ := (((D.naut.ralg_def π).1 hR.ralg) τc).2 z hz
    obtain ⟨a, ha⟩ := odd_rank D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨-n - a + b, ?_⟩
    rw [ha, hb]
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℤ => (n : ℂ)) := Int.cast_injective
  have hcast : ∀ τc, ((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ)) = S τc :=
    fun τc => map_round_cast _ (hint τc)
  refine ⟨ι, fun τc => (S τc).map fun z => ⌊z.re⌋, ?_, ?_⟩
  · intro v hv τ τc hτ a
    rw [hA.jumps v hv τ τc hτ a]
    have := Multiset.count_map_eq_count' (fun n : ℤ => (n : ℂ)) ((S τc).map fun z => ⌊z.re⌋) hinj a
    rw [hcast] at this
    rw [← this]
  · intro τc
    refine ⟨?_, ?_, ?_⟩
    · simp only [S, Multiset.card_map, D.naut.infG_card]
    · apply Multiset.map_injective hinj
      rw [hcast]
      have : (((S τc).map fun z => ⌊z.re⌋).map (fun a => (D.R.t : ℤ) - 1 - a)).map (fun n : ℤ => (n : ℂ))
          = (((S τc).map fun z => ⌊z.re⌋).map (fun n : ℤ => (n : ℂ))).map (fun w => (D.R.t : ℂ) - 1 - w) := by
        simp only [Multiset.map_map, Function.comp_def]
        push_cast
        rfl
      rw [this, hcast]
      simp only [S, hR.anti τc, Multiset.map_map, Function.comp_def]
      refine Multiset.map_congr rfl fun z _ => ?_
      push_cast
      ring
    · intro a ha
      have h1 : (a : ℂ) ∈ S τc := by
        rw [← hcast τc]
        exact Multiset.mem_map_of_mem _ ha
      obtain ⟨z, hz, hza⟩ := Multiset.mem_map.1 h1
      refine hR.window τc z hz a ?_
      rw [← hza]
      push_cast
      ring

end GlobalTheory.TripleGal.Jumps
