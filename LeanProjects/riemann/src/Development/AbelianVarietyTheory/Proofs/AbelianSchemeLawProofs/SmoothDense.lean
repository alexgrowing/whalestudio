import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_smoothLocus_ι_comp {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  simp

theorem smoothDense : SmoothDenseSt := by
  intro K _ _ X f hX hf
  have : LocallyOfFinitePresentation f := inferInstance
  exact f.dense_smoothLocus_of_perfectField.mono
    fun x hx => ⟨f.smoothLocus, hx, smooth_smoothLocus_ι_comp f⟩

end GlobalTheory
