import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFact
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem exists_real_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∃ v : Valuation Ω ℝ≥0, (∀ x : Ω, v x ≤ 1 ↔ x ∈ A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∀ x : Ω, v (s x) = v x) ∧ 0 < v (l : Ω) ∧ v (l : Ω) < 1 := by
  intro l _ Ω _ _ _ A h
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨w, hw, hl⟩ := h
    simpa using (hw ((l : ℕ) : 𝓞 ℚ)).2 hl
  obtain ⟨j, hj⟩ := Formalism.BasicNotions.Examples₂.LB.exists_emb (l := l) A hA
  let v : Valuation Ω ℝ≥0 := (NormedField.valuation (K := PadicAlgCl l)).comap j
  have hv : ∀ x : Ω, v x ≤ 1 ↔ x ∈ A := by
    intro x
    rw [hj]
    exact Iff.rfl
  have he : v.IsEquiv A.valuation := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    rw [hv, A.valuation_le_one_iff]
  refine ⟨v, hv, fun s hs x => ?_, ?_, ?_⟩
  · exact he.eq_iff.2 (GlobalTheory.Dec_valuation_apply_eq ℚ Ω A s hs x)
  · have : CharZero Ω := j.charZero
    have hl : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    exact zero_lt_iff.mpr ((v.ne_zero_iff).2 hl)
  · exact he.lt_one_iff_lt_one.2 hA

end GlobalTheory.RecOne
