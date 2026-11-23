import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LatVac

theorem restrict_liftV_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ κ _ v Φ hΦ
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    let s : (κ → Fv F v) → (κ → Af F) := fun t i => GlobalTheory.AdelicU.singleFin v (t i)
    have hs : Continuous s := continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)
    have hinv : Function.LeftInverse (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) s :=
      fun t => funext fun i => GlobalTheory.AdelicU.evalV_singleFin_self v (t i)
    have hev : Continuous (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    have hce : Topology.IsClosedEmbedding s := hinv.isClosedEmbedding hev hs
    have hmem : g ∘ s ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
      ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding hce⟩
    have e : (fun t : κ → Fv F v => GlobalTheory.WeilM.pureA F (⇑f) g (fun i => GlobalTheory.LatVac.liftV v (t i))) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) • (g ∘ s) := by
      funext t
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end GlobalTheory.LatVac

end
