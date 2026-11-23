import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

noncomputable section
namespace GlobalTheory.SerreOnto
open CategoryTheory.Limits

variable {X T : Scheme.{0}} (i : T ⟶ X)

def unitToPush : GlobalTheory.LB.unitMod X ⟶ (Scheme.Modules.pushforward i).obj (GlobalTheory.LB.unitMod T) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

theorem toPushforward_comp (M : LB X) :
    GlobalTheory.LB.toPushforward M i ≫ ((Scheme.Modules.pushforward i).map (Twist.unitTwistIso (M.pull i)).inv ≫
      (Twist.projIso M i (GlobalTheory.LB.unitMod T)).hom) =
      (Twist.unitTwistIso M).inv ≫ Twist.map M (unitToPush i) := by
  apply Twist.hom_ext
  intro V s j
  change resG T (Twist.le_pull_inf i V j)
      ((i.appLE _ _ (GlobalTheory.LB.pull_inf_le i V (fun _ => j))).hom (GlobalTheory.LB.coord s j)) =
    (i.app _).hom (GlobalTheory.LB.coord s j)
  rw [GlobalTheory.LB.resG_appLE, ← Scheme.Hom.appLE_eq_app]

def kernelIso (M : LB X) (hM : M.IsLB) :
    kernel (GlobalTheory.LB.toPushforward M i) ≅ twist (kernel (unitToPush i)) M :=
  haveI := Twist.preservesFiniteLimits_twistFunctor hM
  kernel.mapIso _ _ (Twist.unitTwistIso M).symm
    ((Scheme.Modules.pushforward i).mapIso (Twist.unitTwistIso (M.pull i)).symm ≪≫
      Twist.projIso M i _) (toPushforward_comp i M) ≪≫
    (PreservesKernel.iso (twistFunctor M) (unitToPush i)).symm

end GlobalTheory.SerreOnto

open CategoryTheory.Limits in

theorem GlobalTheory.surjective_toPushforward_app_top_lbPow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k]
    (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L →
    ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop,
      Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  intro k _ _ X p hp L hL T i _
  letI : Algebra k Γ(X, ⊤) := (p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = p.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r) :=
    fun _ => rfl
  haveI := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : QCoh.IsFiniteQC (kernel (GlobalTheory.SerreOnto.unitToPush i)) :=
    QCoh.IsFiniteQC.of_mono (kernel.ι (GlobalTheory.SerreOnto.unitToPush i))
  filter_upwards [hL.eventually_subsingleton_coh_twist hf (kernel (GlobalTheory.SerreOnto.unitToPush i))]
    with N hN
  have hM : (lbPow L N).IsLB := isLB_lbPow hL.isLB N
  haveI := GlobalTheory.PinchLift.epi_toPushforward_of_closedImm i hM
  let φ := GlobalTheory.LB.toPushforward (lbPow L N) i
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (S.exact_of_f_is_kernel (kernelIsKernel φ)) inferInstance inferInstance
  refine cohOn.app_surjective hS ⊤ ?_
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 (GlobalTheory.SerreOnto.kernelIso i _ hM)).toEquiv.subsingleton_congr.2
    (hN 1 one_pos)
