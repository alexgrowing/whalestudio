import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompAtMtMul
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv

set_option maxHeartbeats 1000000 in

theorem mulFun_eq_one_of_eq_one_on_maxCompact : ∀ (D : D7) (T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) → ∀ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') → (∀ k ∈ GinfC T, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) → χ k = 1) → ∀ u ∈ GinfC T, χ u = 1 :=
  fun D T θ hθ s hs χ hm hK =>
    GlobalTheory.UnitaryChar.char_eq_one D θ T hθ s hs χ hm fun k hk h => hK k hk fun τ => (h τ).symm

end GlobalTheory.FrameEquiv
