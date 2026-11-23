import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleOfFiniteSurjectivePullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_of_finite_surjective_pullback : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X), AlgebraicGeometry.IsNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsFinite f → Function.Surjective f → ∀ L : ReciprocityTheory.ChartRestriction.G.Semi.LB X, L.IsLB → GlobalTheory.IsAmpleLB (L.pull f) → GlobalTheory.IsAmpleLB L := by
  first | exact @GlobalTheory.NormalDescent.isAmpleLB_of_pull | exact GlobalTheory.NormalDescent.isAmpleLB_of_pull | (intros; apply GlobalTheory.NormalDescent.isAmpleLB_of_pull <;> assumption)
