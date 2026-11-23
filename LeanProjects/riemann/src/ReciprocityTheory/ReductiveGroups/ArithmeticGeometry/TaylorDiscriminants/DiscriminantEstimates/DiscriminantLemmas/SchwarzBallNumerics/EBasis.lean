import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne

namespace PI.UnitaryGroupMassFormula.TBNum

open ComplexConjugate

theorem eBasis : ReciprocityTheory.ChartRestriction.G.TB.EBasisSt := by
  unfold ReciprocityTheory.ChartRestriction.G.TB.EBasisSt
  intro E _ _ W _ _ _ _ _ ι _ v hv hcard
  classical
  haveI : FiniteDimensional ℚ W := Module.Finite.trans E W
  have hinj : Function.Injective v := hv.injective
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, hcard, Module.finrank_mul_finrank]
  have hspanE : Submodule.span E (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := by rw [hspanQ]; trivial
    exact Submodule.span_le_restrictScalars ℚ E (Set.range v) hx
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent E (Set.range v)
  let s : Finset ι := Finset.univ.filter (fun i => v i ∈ b)
  have hrange : Set.range (fun i : s => v i) = b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Finset.mem_filter.mp i.2).2
    · intro hx
      obtain ⟨i, rfl⟩ := hbsub hx
      exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
  have hli : LinearIndependent E (fun i : s => v i) := by
    let f : s → b := fun i => ⟨v i, (Finset.mem_filter.mp i.2).2⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hij)
    exact hbli.comp f hf
  have hspan : Submodule.span E (Set.range fun i : s => v i) = ⊤ := by
    rw [hrange, hbspan, hspanE]
  refine ⟨s, ?_, hli, hspan⟩
  have hfr := finrank_span_eq_card hli
  rw [hspan, finrank_top, Fintype.card_coe] at hfr
  exact hfr.symm

end PI.UnitaryGroupMassFormula.TBNum
