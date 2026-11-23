import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedWittNormSquare
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry

noncomputable section

namespace GlobalTheory.Proof.WeightSequenceEntries

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem padZero_eq {a : ℕ} (b : ℕ) (ν : DomWeight a) (j : Fin b) :
    PaddedWittNormSquare.padZero b ν j = PaddedLastEntry.padZero b ν j := rfl

theorem lastEntry_eq {a : ℕ} (ν : DomWeight a) : PaddedWittNormSquare.lastEntry ν = PaddedLastEntry.lastEntry ν := rfl

theorem normSq_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    PaddedWittNormSquare.normSq lam v = PaddedLastEntry.invNormSq lam v := rfl

theorem unitSq_eq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    PaddedWittNormSquare.unitNormSq r z = PaddedLastEntry.unitSq r z := rfl

theorem tmax_eq {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) :
    PaddedWittNormSquare.tmax b ν Om S = PaddedLastEntry.tmax b ν S Om := rfl

theorem opNormSqLe_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' T t ↔ PaddedLastEntry.OpNormSqLe lam lam' T t := by
  unfold PaddedWittNormSquare.OpNormSqLe PaddedLastEntry.OpNormSqLe
  simp only [normSq_eq]

theorem stepWeights_iff {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) :
    (∃ s' s : ℤ, PaddedWittNormSquare.IsStepWeight lam ν lam' s' s) ↔ PaddedLastEntry.StepWeights lam ν lam' := by
  unfold PaddedWittNormSquare.IsStepWeight PaddedLastEntry.StepWeights
  constructor
  · rintro ⟨s', s, hν, hpos, hpad⟩
    exact ⟨hpos, ⟨s', hν⟩, ⟨s, fun j => (hpad j).trans (padZero_eq b ν j)⟩⟩
  · rintro ⟨hpos, ⟨s', hν⟩, ⟨s, hpad⟩⟩
    exact ⟨s', s, hν, hpos, fun j => (hpad j).trans (padZero_eq b ν j).symm⟩

theorem stepWeights_family_iff {ι : Type} {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) :
    (∃ s' s : ι → ℤ, ∀ τ, PaddedWittNormSquare.IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) ↔
      ∀ τ, PaddedLastEntry.StepWeights (lam τ) (ν τ) (lam' τ) := by
  constructor
  · rintro ⟨s', s, h⟩ τ
    exact (stepWeights_iff (lam τ) (ν τ) (lam' τ)).1 ⟨s' τ, s τ, h τ⟩
  · intro h
    choose s' s hs using fun τ => (stepWeights_iff (lam τ) (ν τ) (lam' τ)).2 (h τ)
    exact ⟨s', s, hs⟩

theorem guard_iff {ι : Type} {a b : ℕ} (hab : a ≤ b) (ν : ι → DomWeight a) :
    (∀ τ, a < b ∨ PaddedWittNormSquare.lastEntry (ν τ) = 0) ↔ (a = b → ∀ τ, PaddedLastEntry.lastEntry (ν τ) = 0) := by
  constructor
  · intro h heq τ
    rcases h τ with hlt | h0
    · exact absurd heq (ne_of_lt hlt)
    · exact (lastEntry_eq (ν τ)).symm.trans h0
  · intro h τ
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ((lastEntry_eq (ν τ)).trans (h heq τ))

theorem growth_iff {ι : Type} [Fintype ι] {a b : ℕ} (G : VCx ι a b → ℂ) (S : ℝ) (r : ι → ℝ) :
    (∀ z, ‖G z‖ ≤ S * Real.exp (PaddedWittNormSquare.unitNormSq r z / 2)) ↔
      ∀ z, ‖G z‖ ≤ S * Real.exp (PaddedLastEntry.unitSq r z / 2) := by
  simp only [unitSq_eq]

theorem conclusion_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b)
    (G : VCx ι a b → ℂ) (S : ℝ) (Om : ι → ℝ) (cD : ι → ℂ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedWittNormSquare.lastEntry (ν τ)) (PaddedWittNormSquare.tmax b ν Om S) ↔
      PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedLastEntry.lastEntry (ν τ)) (PaddedLastEntry.tmax b ν S Om) := by
  simp only [opNormSqLe_iff, tmax_eq, lastEntry_eq]

theorem blockBound_iff : PaddedWittNormSquare.BlockBound ↔ PaddedLastEntry.BlockBound := by
  unfold PaddedWittNormSquare.BlockBound PaddedLastEntry.BlockBound
  constructor
  · intro h ι _ a b hab lam ν lam' hstep hguard r Om cD hr hOm hc G S hG hgrowth
    obtain ⟨s', s, hs⟩ := (stepWeights_family_iff lam ν lam').2 hstep
    exact (conclusion_iff lam ν lam' G S Om cD).1
      (h ι a b hab lam ν lam' s' s hs ((guard_iff hab ν).2 hguard) G S r Om cD hG hr
        ((growth_iff G S r).2 hgrowth) hOm hc)
  · intro h ι _ a b hab lam ν lam' s' s hs hguard G S r Om cD hG hr hgrowth hOm hc
    exact (conclusion_iff lam ν lam' G S Om cD).2
      (h ι a b hab lam ν lam' ((stepWeights_family_iff lam ν lam').1 ⟨s', s, hs⟩)
        ((guard_iff hab ν).1 hguard) r Om cD hr hOm hc G S hG ((growth_iff G S r).1 hgrowth))

end GlobalTheory.Proof.WeightSequenceEntries
