import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.Present

def toModPullZPowIso {X Y : Scheme.{0}} {L : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hL : L.IsLB) (f : Y ⟶ X) (m : ℤ) :
    GlobalTheory.LB.toMod ((GlobalTheory.lbZPow L m).pull f) ≅ GlobalTheory.LB.toMod (GlobalTheory.lbZPow (L.pull f) m) :=
  (GlobalTheory.Twist.unitTwistIso _).symm ≪≫ (GlobalTheory.Twist.twistZPullIso f hL _ m).symm ≪≫ GlobalTheory.Twist.unitTwistIso _

theorem exists_coherent_epi_restrict {X : Scheme.{0}} [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X)
    (hH : GlobalTheory.IsAmpleLB H) (O : X.Opens) (E : (O : Scheme.{0}).Modules) (hE : IsCoherent E) :
    ∃ P : X.Modules, IsCoherent P ∧ ∃ f : P.restrict O.ι ⟶ E, Epi f := by
  haveI : CompactSpace (O : Scheme.{0}) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  haveI : GlobalTheory.QCoh.IsFiniteQC E := ⟨hE.1, hE.2⟩
  have hA := hH.pull_of_isOpenImmersion O.ι
  obtain ⟨n, k, φ, hφ⟩ := (hA.eventually_exists_epi_sigma E).exists
  have hL := GlobalTheory.Twist.isLB_lbZPow hH.isLB (-n)
  haveI : GlobalTheory.QCoh.IsFiniteQC (GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))) := (GlobalTheory.VB.isVB_toMod hL).isFiniteQC
  let P : X.Modules := ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow H (-n))
  have hP : GlobalTheory.QCoh.IsFiniteQC P := inferInstance
  let e : P.restrict O.ι ≅ ∐ fun _ : Fin k => GlobalTheory.LB.toMod (GlobalTheory.lbZPow (H.pull O.ι) (-n)) :=
    (Scheme.Modules.restrictFunctorIsoPullback O.ι).app P ≪≫
      PreservesCoproduct.iso (Scheme.Modules.pullback O.ι) _ ≪≫
      Sigma.mapIso (fun _ => GlobalTheory.LB.pullbackIso hL O.ι ≪≫ toModPullZPowIso hH.isLB O.ι (-n))
  exact ⟨P, ⟨hP.1, hP.2⟩, e.hom ≫ φ, epi_comp _ _⟩

end GlobalTheory.CompanionTheory.GE.Present
