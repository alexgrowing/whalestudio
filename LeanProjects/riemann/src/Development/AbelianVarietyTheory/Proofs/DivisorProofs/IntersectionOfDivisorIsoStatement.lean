import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionOfDivisorIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_of_divisor_iso : ∀ (F : Type) [Field F] (Y Y' : Var F) (Δ : Y.Dv) (Δ' : Y'.Dv) (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ), DivIso Δ Δ' φ ψ u → Y.inter (fun _ => Δ) = Y'.inter (fun _ => Δ') := by
  first | exact @GlobalTheory.ShFam.GalCarry.Deg.inter_eq_of_divIso | exact GlobalTheory.ShFam.GalCarry.Deg.inter_eq_of_divIso | (intros; apply GlobalTheory.ShFam.GalCarry.Deg.inter_eq_of_divIso <;> assumption)
