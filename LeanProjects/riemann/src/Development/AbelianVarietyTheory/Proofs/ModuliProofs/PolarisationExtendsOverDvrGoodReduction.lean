import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleExtendedPrincipalPolarisationDvrStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKTrivialOfPrincipalGenericFibreDvr

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PolExtendDVR

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB Y} {M : LB X} {φ : Y ⟶ X} (h : LBIso L (M.pull φ)) (g : Z ⟶ Y) :
    LBIso (L.pull g) (M.pull (g ≫ φ)) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L g g rfl)
    (chartPullSame M (fun _ : PUnit => g ≫ φ) (fun _ => φ) (fun _ => 1) g fun _ => rfl) h

theorem exists_baseChange (hB : PolBaseChangeSt) {V K V' K' : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (a : V →+* V') (ha : Function.Injective a)
    (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left)
    (hφ : IsGrpPullback P.A B (spMap (algebraMap V K)) φ) (hL : LBIso P.L (M.L.L.pull φ)) :
    ∃ (P' : PolAV (Sp K')) (M' : GlobalTheory.UU.CP ((Over.pullback (spMap a)).obj B))
      (φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left),
      IsGrpPullback P'.A ((Over.pullback (spMap a)).obj B) (spMap (algebraMap V' K')) φ' ∧
        LBIso P'.L (M'.L.L.pull φ') ∧ LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := by
  have hi : Function.Injective ((algebraMap V' K').comp a) := (IsFractionRing.injective V' K').comp ha
  let b : K →+* K' := IsFractionRing.lift hi
  have hb : b.comp (algebraMap V K) = (algebraMap V' K').comp a :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hi x
  have hs : spMap b ≫ spMap (algebraMap V K) = spMap (algebraMap V' K') ≫ spMap a := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hB _ _ (spMap b) P
  have gp : IsGrpPullback P'.A P.A (spMap b) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  have hπ := isGrpPullback_pullback B (spMap a)
  have gc := (gp.comp hφ).congr hs rfl
  obtain ⟨M', w, hw⟩ := GlobalTheory.UU.exists_pull M (GlobalTheory.UU.toBase_mul_pullback B (spMap a))
  have hM : LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := ⟨w, hw.gen⟩
  let φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left :=
    pullback.lift (g ≫ φ) (P'.A.hom ≫ spMap (algebraMap V' K')) (gc.1.w.trans (Category.assoc _ _ _).symm)
  have e : φ' ≫ pullback.fst B.hom (spMap a) = g ≫ φ := pullback.lift_fst _ _ _
  refine ⟨P', M', φ', hπ.cancel (gc.congr rfl e.symm) (pullback.lift_snd _ _ _), ?_, hM⟩
  have i₁ : LBIso P'.L (M.L.L.pull (g ≫ φ)) :=
    LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB M.L.isLB _) (LBIso.symm ⟨t, ht⟩) (lbIso_pull_comp hL g)
  have i₂ := lbIso_pull_comp hM φ'
  rw [e] at i₂
  exact LBIso.trans P'.isLB (pull_isLB M.L.isLB _) (pull_isLB M'.L.isLB _) i₁ i₂.symm

end GlobalTheory.PolExtendDVR

namespace GlobalTheory

open PolExtendDVR IsLocalRing in

theorem polarisation_extends_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L ∧ KTriv B M.L.L := by
  intro h h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ hL
  let V' := AdicCompletion (maximalIdeal V) V
  obtain ⟨P', M', φ', hφ', hL', hM⟩ := exists_baseChange (K' := FractionRing V') h.polBaseChange (algebraMap V V')
    (algebraMap_adicCompletion_injective_of_dvr V) P B M φ hφ hL
  have hπ := isGrpPullback_pullback B (spMap (algebraMap V V'))
  have hB' := PolPull.isAbelianScheme_of_isGrpPullback hB hπ
  have hA' := GlobalTheory.T.relAmple_extended_principalPolarisation_dvr h h₂ V' (FractionRing V') P' _ M' φ' hB' hφ' hL' inferInstance
  have : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hA : RelAmple B M.L.L :=
    AmpleDescent.relAmple_of_faithfullyFlat V V' B _ _ M.L.L M'.L.L hB hπ M.L.isLB M'.L.isLB hM hA'
  exact ⟨hA, KTrivSpread.kTriv_of_generic_fibre h V K P B M φ hB hφ hL hA⟩

end GlobalTheory
