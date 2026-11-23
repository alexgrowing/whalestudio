import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIntegralFlagModelOfSmoothCoefficientFielStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushInvertibleOfHasTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFibrewiseNonvanishingThetaSectionOfSmoothMode
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS.TorFlagEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem torFlag_of_model (Y : Model Xo c (RingHom.id c.F)) (hs : SmoothOfRelativeDimension Dw.dim Y.s)
    (hb : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (LogKS.boundary Y)) (hk : LogKS.HasLogKS Y.t Y.s (LogKS.interior Y))
    (hp : PushInvertible Y.t.G Y.t.PP.L) : Nonempty (TorFlag Xo c) :=
  ⟨⟨Y, hs, hb, hk, (GlobalTheory.T.nonempty_integralFlagModel_of_smooth_coefficientField E H Dw l Xo c Y hs hp).some⟩⟩

theorem nonempty_torFlag (hP : GlobalTheory.CovTop.Hypotheses₂) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ dimFlag Dw → Nonempty (TorFlag Xo c) := by
  intro E _ _ _ H Dw l Xo c hd
  obtain ⟨Y, hs, hb, hk⟩ := hP.p1 E H Dw (one_le_of_dimFlag hd) l Xo c
  exact torFlag_of_model Y hs hb hk
    (pushInvertible_of_hasTheta Y (GlobalTheory.ThetaNormal.hasTheta_of_smooth E H Dw (one_le_of_dimFlag hd) l Xo c Y hs))

end GlobalTheory.CompHS.TorFlagEx
