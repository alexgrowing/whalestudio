import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpansAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhereStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.KTrivSpread

namespace GlobalTheory.KTrivGenericPt

theorem spMap_eq_lift_comp_jK {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) :
    spMap ψ = spMap (IsFractionRing.lift (K := FractionRing R) hψ) ≫ Out.jK R := by
  rw [Out.jK, spMap, spMap, ← Spec.map_comp]
  congr 1
  ext r
  simp

theorem trivAlong_field {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {R : Type} [CommRing R] [IsDomain R]
    {g : Sp R ⟶ S} (h : TrivAlong A L (Out.jK R ≫ g)) {F : Type} [Field F] (ψ : R →+* F)
    (hψ : Function.Injective ψ) : TrivAlong A L (spMap ψ ≫ g) := by
  rw [spMap_eq_lift_comp_jK ψ hψ, Category.assoc]
  exact h.comp _

end GlobalTheory.KTrivGenericPt

open GlobalTheory.KTrivGenericPt in

theorem GlobalTheory.KTrivGenericPt.kTriv_of_polAt_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), IsProper t.G.hom → RelAmple t.G t.PP.L → GlobalTheory.LN.PolAt t (jK R) → KTriv t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ _ t hP ha hpol
  haveI : IsProper t.G.hom := hP
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  have hgen : TrivAlong t.G t.PP.L (Out.jK R) :=
    trivAlong_of_kTriv (isGrpPullback_pullback t.G (Out.jK R)) t.PP.isLB hpol.2.2
  have hgen' : TrivAlong t.G t.PP.L (Out.jK R ≫ 𝟙 (Sp R)) := by rw [Category.comp_id]; exact hgen
  refine kTriv_of_primes hG R t.G hA t.PP.L t.PP.isLB ha fun p => ?_
  let O := Localization.AtPrime p.asIdeal
  have hO : Function.Injective (algebraMap R O) := IsLocalization.injective O p.asIdeal.primeCompl_le_nonZeroDivisors
  have hp : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  by_cases hf : IsField O
  · refine ⟨O, inferInstance, algebraMap R O, ⟨_, hp⟩, ?_⟩
    letI := hf.toField
    have := trivAlong_field hgen' (algebraMap R O) hO
    rwa [Category.comp_id] at this
  · obtain ⟨V, _, _, _, ρ, h1, h2⟩ := exists_dvr O hf
    have hρ : Function.Injective (ρ.comp (algebraMap R O)) := h1.comp hO
    have : CharZero V := charZero_of_injective_ringHom hρ
    refine ⟨V, inferInstance, ρ.comp (algebraMap R O), ⟨IsLocalRing.closedPoint V, ?_⟩, ?_⟩
    · rw [PrimeSpectrum.comap_comp_apply, IsLocalRing.comap_closedPoint, hp]
    · have key := trivAlong_dvr hG (𝟙 (Sp R)) hA t.PP t.cub ha V (spMap (ρ.comp (algebraMap R O))) ?_
      · rwa [Category.comp_id] at key
      · let F := AlgebraicClosure (FractionRing V)
        have H' := trivAlong_field hgen'
          ((algebraMap (FractionRing V) F).comp ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O))))
          ((algebraMap (FractionRing V) F).injective.comp ((IsFractionRing.injective V (FractionRing V)).comp hρ))
        have e : (Out.TF (R := V) F).hom ≫ spMap (ρ.comp (algebraMap R O)) = spMap ((algebraMap (FractionRing V) F).comp
            ((algebraMap V (FractionRing V)).comp (ρ.comp (algebraMap R O)))) :=
          (congrArg (· ≫ _) (Spec.map_comp _ _).symm).trans (Spec.map_comp _ _).symm
        rw [← e, Category.assoc] at H'
        exact H'
