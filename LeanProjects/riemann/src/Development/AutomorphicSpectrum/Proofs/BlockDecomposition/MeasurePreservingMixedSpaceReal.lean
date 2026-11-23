import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
open MeasureTheory NumberField
open scoped Classical

namespace GlobalTheory.CompanionTheory.RealAdele

theorem isEmpty_isComplex : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun a => by
    have h : a.1 = Ad3.GP.wR := Subsingleton.elim _ _
    have h2 := a.2
    rw [h] at h2
    exact InfinitePlace.not_isReal_iff_isComplex.mpr h2 Ad3.GP.wR_isReal⟩

end GlobalTheory.CompanionTheory.RealAdele
