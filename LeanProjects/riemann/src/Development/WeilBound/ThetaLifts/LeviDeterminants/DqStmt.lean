import Development.WeilBound.ThetaLifts.LeviDeterminants.NormIteratedFDerivIdLeOneAdd

namespace PositivityTheory.ThKF0

def SchwartzDq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (a : V) (L : V →L[ℝ] ℝ) (f : SchwartzMap V ℂ)
    (G : ℝ → SchwartzMap V ℂ), (∀ t x, G t x = Lib.hl a L t f x) → ∀ T : SchwartzMap V ℂ →L[ℂ] ℂ,
      HasDerivAt (fun t => T (G t)) (T (Lib.dop a L f)) 0

end PositivityTheory.ThKF0
