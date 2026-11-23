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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KTypeGelf

theorem gelf_mem_typeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  intro D θ V S M hθ ψ hψ Y₀ τ k
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set ρ := GlobalTheory.KTypeProj.rhoK θ M with hρ
  have hGsm : ∀ f ∈ G, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    fun k τs Xs h g => (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth k τs Xs h g
  have hL := GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k

  let g0 : GlobalTheory.Mem.AutSpace.SmFun θ V →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun φ => gelf θ V τ k φ
      map_add' := fun φ ψ' => hL.add _ φ.2 _ ψ'.2
      map_smul' := fun c φ => hL.smul c φ }
  obtain ⟨L, hLe⟩ := LinearMap.exists_extend g0
  have hLa : ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, L φ = gelf θ V τ k φ := fun φ hφ => by
    have := congrArg (fun F => F ⟨φ, hφ⟩) hLe
    simpa [g0] using this
  have hgel0 : gelf θ V τ k 0 = 0 := by
    have := hL.smul 0 0
    simpa using this
  let Q : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | f ∈ G ∧ gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G}
      add_mem' := fun {a b} ha hb => by
        refine ⟨G.add_mem ha.1 hb.1, ?_⟩
        rw [hL.add a (hGsm a ha.1) b (hGsm b hb.1)]
        exact Submodule.add_mem _ ha.2 hb.2
      zero_mem' := ⟨G.zero_mem, by rw [hgel0]; exact Submodule.zero_mem _⟩
      smul_mem' := fun c f hf => by
        refine ⟨G.smul_mem c hf.1, ?_⟩
        rw [hL.smul c f]
        exact Submodule.smul_mem _ c hf.2 }
  have hle : GlobalTheory.KTypeProj.typeSpan ρ Y₀ G ≤ Q := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    refine ⟨hTw, ?_⟩
    have hmap : Y₀.map (L ∘ₗ T) ≤ G := by
      rintro _ ⟨v, hv, rfl⟩
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      show L (T v) ∈ G
      rw [hLa _ (hGsm _ hTv)]
      exact GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ) τ k _ hTv
    have hcomm : ∀ i, ∀ v ∈ Y₀, (L ∘ₗ T) (ρ i v) = ρ i ((L ∘ₗ T) v) := by
      intro i v hv
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      have hs := hGsm _ hTv
      simp only [LinearMap.comp_apply]
      rw [hT.2 i v hv, hLa _ (hs), hρ, GlobalTheory.KTypeProj.rhoK, GlobalTheory.KTypeProj.rTrL_apply, GlobalTheory.KTypeProj.rTrL_apply,
        hLa _ (GlobalTheory.RegSch.CentreRight.rTr_mem_all hθ _ hs), GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ τ k hs]
    have := GlobalTheory.KTypeProj.map_le_typeSpan ρ (L ∘ₗ T) hmap hcomm ⟨w, hw, rfl⟩
    simpa [hLa _ (hGsm _ hTw)] using this
  intro f hf
  exact (hle hf).2

end GlobalTheory.KTypeGelf
