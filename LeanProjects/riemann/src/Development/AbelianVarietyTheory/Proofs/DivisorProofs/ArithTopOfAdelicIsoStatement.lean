import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithTopOfAdelicIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializationMapCompUniversalSection
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.GalCarry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_top_of_adelic_iso : ∀ (F : Type) [Field F] [NumberField F] (C : GlobalTheory.TrueGeo.CxSt F) (Y Y' : Var F) (A : GlobalTheory.TrueGeo.Adl C Y) (A' : GlobalTheory.TrueGeo.Adl C Y') (φ : Y.X ≅ Y'.X) (ψ : Y'.Fn →+* Y.Fn) (u : Y.Fnˣ), AdlIso A A' φ ψ u → A.deg = A'.deg → ∀ t : ℝ, A'.IsArTop t → A.IsArTop t := by
  first | exact @GlobalTheory.ShFam.GalCarry.isArTop_of_adlIso | exact GlobalTheory.ShFam.GalCarry.isArTop_of_adlIso | (intros; apply GlobalTheory.ShFam.GalCarry.isArTop_of_adlIso <;> assumption)
