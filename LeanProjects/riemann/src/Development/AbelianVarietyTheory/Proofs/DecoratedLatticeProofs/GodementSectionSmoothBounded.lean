import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphSmooth

open GlobalTheory.SiegelSet (IsRealLine lineDer)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem isRealLine_oneP (hθ : IsInfFam θ) (V : HSp D) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  refine ⟨placeOf D τ, embOverOf D τ, X, hX, fun t => ?_⟩
  obtain ⟨x, hx⟩ := exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  refine ⟨x, ?_, ?_⟩
  · rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl x]
  · rw [GlobalTheory.Orb.archMat_eq_archEquiv _ (isCMExt_host D), hx]

theorem mem_smFun_of_isSm (hθ : IsInfFam θ) {f : GA D V → ℂ} (h : GlobalTheory.UAut.IsSm D.sp.cm.sig V.gram f) :
    f ∈ SmFun θ V :=
  fun k τs Xs hX g => h k (fun i => oneP θ V (τs i) (Xs i)) (fun i => isRealLine_oneP hθ V (hX i)) g

def derSpan (V : HSp D) (f : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  Submodule.span ℂ {g | ∃ l : List (ℝ → GA D V), (∀ γ ∈ l, IsRealLine D.sp.cm.sig V.gram γ) ∧ g = l.foldr lineDer f}

theorem derSpan_le (hθ : IsInfFam θ) {f : GA D V → ℂ} (hf : f ∈ SmFun θ V) : derSpan V f ≤ SmFun θ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨l, hl, rfl⟩
  induction l with
  | nil => exact hf
  | cons γ l ih =>
    obtain ⟨p, hp, rfl⟩ := (hl γ List.mem_cons_self).eq_oneP hθ
    exact GlobalTheory.Mem.AutSpace.Rder_mem (ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)) hp

end GlobalTheory.SphSmooth

end
