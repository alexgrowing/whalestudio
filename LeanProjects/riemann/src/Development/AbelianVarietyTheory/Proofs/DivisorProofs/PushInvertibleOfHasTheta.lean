import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
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

theorem isDedFrac_id : GlobalTheory.Models.IsDedFrac (RingHom.id c.F) :=
  ⟨⟨inferInstance, inferInstance⟩, inferInstance, inferInstance⟩

theorem pushInvertible_of_hasTheta (Y : Model Xo c (RingHom.id c.F)) (hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L) :
    PushInvertible Y.t.G Y.t.PP.L :=
  GlobalTheory.PushInv.pushInvertible_of_model GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1 GlobalTheory.allSixLaws.2.2.1 E H Dw l _ _ _ _ _ _ Y.oF _
    (RingHom.id c.F)
    ⟨Y.X, Y.s, Y.normal, Y.proj, Y.flat, Y.jQ, Y.jQ_over, Y.jQ_open, Y.jQ_dense, Y.t, Y.m, Y.ab_gen⟩ isDedFrac_id hθ

theorem one_le_of_dimFlag (h : 1 ≤ dimFlag Dw) : 1 ≤ Dw.p + Dw.q := by
  by_contra h0
  have : Dw.p + Dw.q = 0 := by omega
  simp [dimFlag, Formalism.DegreeFormula.dimFl, this] at h

end GlobalTheory.CompHS.TorFlagEx
