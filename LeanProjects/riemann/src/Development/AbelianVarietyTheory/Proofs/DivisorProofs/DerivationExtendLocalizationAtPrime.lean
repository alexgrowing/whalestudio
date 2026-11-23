import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem derivation_extend_localization_atPrime (F A R : Type) [CommRing F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] (D : Derivation F A R) :
    ∃ D' : Derivation F R R, ∀ a, D' (algebraMap A R a) = D a := by
  haveI : Algebra.FormallyEtale A R := Algebra.FormallyEtale.of_isLocalization P.primeCompl
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale F A R
  refine ⟨(hb.lift D.liftKaehlerDifferential).compDer (KaehlerDifferential.D F R), fun a => ?_⟩
  show hb.lift D.liftKaehlerDifferential (KaehlerDifferential.D F R (algebraMap A R a)) = D a
  rw [← KaehlerDifferential.map_D F F A R, hb.lift_eq, Derivation.liftKaehlerDifferential_comp_D]

end GlobalTheory
