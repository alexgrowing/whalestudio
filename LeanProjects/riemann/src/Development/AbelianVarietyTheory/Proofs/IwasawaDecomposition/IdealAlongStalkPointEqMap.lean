import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferWithFunction
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TraitStalk

theorem idlAlong_spMap_fromSpecStalk : ∀ (T : Scheme.{0}) (v : T) (J : T.IdealSheafData) (W : Type) [CommRing W] [IsLocalRing W]
    (g : T.presheaf.stalk v →+* W), IsLocalHom g → idlAlong J (spMap g ≫ T.fromSpecStalk v) = (FinalTheorems.stalkId J v).map g :=
  fun _ v J _ _ _ g _ => GlobalTheory.PolDiv.idlAlong_fromSpecStalk J v g

end GlobalTheory.TraitStalk
