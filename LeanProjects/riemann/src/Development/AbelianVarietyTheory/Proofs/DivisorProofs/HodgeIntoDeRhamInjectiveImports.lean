import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB

namespace GlobalTheory.HodgeSub

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def Corr {V : T.Opens} (hV : IsAffineOpen V) (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V))
    (c : primDR (onAff A hV)) : Prop :=
  ∀ (v : epsR Γ(T, V) ⟶ onAff A hV) (h : HdR (onAff A hV)), IsLieImage h v →
    ∀ (w : (v.left ≫ pullback.fst A.hom hV.fromSpec) ≫ A.hom =
        (Pdiv.specO Γ(T, V) (DualNumber Γ(T, V))).hom ≫ hV.fromSpec)
      (we : sec (epsZero Γ(T, V)) ≫ v.left ≫ pullback.fst A.hom hV.fromSpec =
        hV.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A),
      h c = (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom
        ((GlobalTheory.TanFibre.form w we).app ⊤
          (GlobalTheory.QCoh.pullbackSections hV.fromSpec (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)
            hV.fromSpec_preimage_self.ge s))

end GlobalTheory.HodgeSub
