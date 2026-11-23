import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FiberLocalization.EqZeroOfFiberEquivariant
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace

namespace PositivityTheory.PfBern.Loc

theorem sb_eq_SC (X : Type*) [TopologicalSpace X] : GlobalTheory.SplitWeil.SB X = SC X :=
  rfl

example (X : Type*) [TopologicalSpace X] (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X)) : Distr X := D

theorem eq_zero_of_fiber_equivariant_SB {X : Type*} [TopologicalSpace X] {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [TotallyDisconnectedSpace Y]
    {ι : Type*} {p : X → Y} (hp : Continuous p)
    (e : ι → X ≃ₜ X) (χ : ι → ℂ) (he : ∀ i x, p (e i x) = p x)
    (hfib : ∀ (y : Y) (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X)),
      (∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) →
      (∀ f : GlobalTheory.SplitWeil.SB X, Function.support (f : X → ℂ) ⊆ (p ⁻¹' {y})ᶜ → D f = 0) → D = 0)
    (D : Module.Dual ℂ (GlobalTheory.SplitWeil.SB X))
    (hD : ∀ (i : ι) (f : GlobalTheory.SplitWeil.SB X),
        D ⟨fun x => (f : X → ℂ) (e i x), f.2.1.comp_continuous (e i).continuous,
          f.2.2.comp_homeomorph (e i)⟩ = χ i * D f) : D = 0 :=
  eq_zero_of_fiber_equivariant (D := D) hp e χ he (fun y D' hD' hs => hfib y D' hD' hs) hD

end PositivityTheory.PfBern.Loc
