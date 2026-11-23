import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LgOfSingleNegOneEqNeg
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lgOf_single_neg_one_eq_neg : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e) (a : Sym E) (v : HeightOneSpectrum (𝓞 F)) (ε : TrueGeo.Ext v) (y : AlgPt Y.Y), lgOf Y (Finsupp.single a (-1)) v ε y = -lgOf Y (Finsupp.single a 1) v ε y + Real.log (ε.w (valAt y.1 (genAt (divOf Y (expo Dw (Finsupp.single a (-1)))) (below y.1) * genAt (divOf Y (expo Dw (Finsupp.single a 1))) (below y.1)))) := by
  first | exact @GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg | exact GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg | (intros; apply GlobalTheory.Adopt.lgOf_single_neg_one_eq_neg <;> assumption)
