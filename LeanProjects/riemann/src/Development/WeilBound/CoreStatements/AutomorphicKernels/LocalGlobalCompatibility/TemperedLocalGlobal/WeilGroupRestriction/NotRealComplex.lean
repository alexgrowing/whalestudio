import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.SplitLift

noncomputable section

open NumberField

namespace PositivityTheory.Pf1.CLGD.K

namespace LKW

theorem not_real_complex (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

theorem wbc_of (h : UpperTheory.CBC.LitCBC2) : WBC := by
  intro F M _ _ _ _ _ _ hF hM hp n hn π
  rcases (h F M hp (Or.inr hF) (Or.inr hM) n hn).1 (.cx π) with ⟨η, hη, hi⟩ | ⟨P, hw, hinf, -⟩
  · exact Or.inl ⟨η, hη.1, hη.2.1, hη.2.2, hi⟩
  · cases P with
    | cx P => exact Or.inr ⟨P, hw, fun τ m hm => hinf τ m hm⟩
    | re P => exact (not_real_complex M inferInstance hM).elim

end LKW

theorem kKW : UpperTheory.CBC.LitCBC2 → WBC := LKW.wbc_of

end PositivityTheory.Pf1.CLGD.K
