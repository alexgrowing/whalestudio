import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidifiedSymmetricLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTrivialOfGeometricFibresStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open MonoidalCategory CartesianMonoidalCategory Limits
open GlobalTheory.CechPic (Pic cls lam)
open MonObj
open scoped CategoryTheory.Obj

theorem GlobalTheory.ThetaRR.exists_isTheta : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p → ∀ (P : PPAS S), P.HasTheta → ∃ L : LB P.A.left, IsTheta P L := by
  intro k _ S p hS P ⟨M, hM, hsym, hc⟩
  have := P.isAb.comm
  have := P.isAb.proper
  have := P.isAb.smooth
  have : IsLocallyNoetherian S := by
    have := hS.isDomain
    have := hS.finite
    have : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
    have := (isProper_and_exists_isAmpleLB_of_isProjOver hS.isProjOver).1
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨M', hM', hrig, hsym', hlam⟩ := GlobalTheory.T.exists_rigidified_symmetric_line_bundle S P.A M hM hsym
  have hc' : P.c = lam (cls M' hM') (fst P.A P.A) (snd P.A P.A) := hc.trans hlam.symm
  have hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S),
      Out.RelAmple ((Over.pullback y).obj P.A) (M'.pull (pullback.fst P.A.hom y)) ∧
        Out.KTriv ((Over.pullback y).obj P.A) (M'.pull (pullback.fst P.A.hom y)) := by
    intro K _ _ y
    obtain ⟨L₀, h₀, ha, hk, e⟩ := P.isPol.2.2 K y
    have h := isGrpPullback_pullback P.A y
    have hB : IsAbelianScheme ((Over.pullback y).obj P.A) :=
      GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb h
    refine GlobalTheory.T.ample_trivial_of_same_polarization K _ hB L₀ h₀ ha hk _ (pull_isLB hM' _) ?_
    rw [← e, hc', IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, CechPic.pull_lam, lift_fst, lift_snd, CechPic.cls_pull hM',
      CechPic.lam_pull_of_isGrpPullback h]
    rfl
  have hamp : Out.RelAmple P.A M' := ProperFinite.relAmple_of_geometricFibres P.A hM' fun K _ _ y => by
    have : IsProper ((Over.pullback y).obj P.A).hom := inferInstanceAs (IsProper (pullback.snd P.A.hom y))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM' _)).1 (hfib K y).1
  exact ⟨M', hM', hrig, hsym', hamp, GlobalTheory.T.k_trivial_of_geometric_fibres S P.A P.isAb M' hM' hamp fun K _ _ y => (hfib K y).2, hc'⟩
