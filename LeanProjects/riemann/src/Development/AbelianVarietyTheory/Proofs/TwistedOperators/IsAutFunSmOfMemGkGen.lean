import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeAdm

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def smAut (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f}
  add_mem' := fun ha hb => GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb
  zero_mem' := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V
  smul_mem' := fun c _ ha => GlobalTheory.Mem.AutSpace.isAutFunSm_smul c ha

theorem isAutFunSm_of_mem_gkGen (hθ : IsInfFam θ) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, IsAutFunSm θ V f := by
  have hA : GlobalTheory.CuspGK.IsGKSub θ M (smAut θ V) :=
    ⟨fun τ g hg f hf => GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf τ g hg.1,
      fun τ X hX f hf => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf⟩
  exact fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := smAut θ V) hψ hA hf

theorem level_gkGen {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g := by
  obtain ⟨U, hU, hψU⟩ := hψ.level
  let A : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g}
      add_mem' := fun ha hb u hu hu' g => by simp only [Pi.add_apply, ha u hu hu' g, hb u hu hu' g]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c f hf u hu hu' g => by simp only [Pi.smul_apply, hf u hu hu' g] }
  have hA : GlobalTheory.CuspGK.IsGKSub θ M A := by
    refine ⟨fun τ g _ f hf u hu hu' x => ?_, fun τ X _ f hf u hu hu' x => ?_⟩
    · show f (x * u * atTau θ V τ g) = f (x * atTau θ V τ g)
      rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) hu',
        ← mul_assoc]
      exact hf u hu hu' _
    · have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hu' τ X f) x
      rw [show rTr V u f = f from funext (hf u hu hu')] at this
      exact this.symm
  exact ⟨U, hU, fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := A) (fun u hu hu' g => hψU u hu hu' g) hA hf⟩

theorem gelf_mem_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (τ : D.what₂.Tau) (k : ℕ) :
    ∀ f ∈ A, gelf θ V τ k f ∈ A := by
  intro f hf
  have hC : ∀ Z, ∀ g ∈ A, RderC θ V τ Z g ∈ A := fun Z g hg => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact A.add_mem (hA.lie τ _ h1 g hg) (A.smul_mem _ (hA.lie τ _ h2 g hg))
  have key : ∀ l : List ((GA D V → ℂ) → (GA D V → ℂ)), (∀ F ∈ l, ∀ g ∈ A, F g ∈ A) →
      l.foldr (fun F acc => F acc) f ∈ A := by
    intro l hl
    induction l with
    | nil => exact hf
    | cons F l ih => exact hl F (by simp) _ (ih fun F' hF' => hl F' (by simp [hF']))
  refine Submodule.sum_mem _ fun idx _ => key _ fun F hF => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hF
  exact hC _

end GlobalTheory.KTypeAdm

end
