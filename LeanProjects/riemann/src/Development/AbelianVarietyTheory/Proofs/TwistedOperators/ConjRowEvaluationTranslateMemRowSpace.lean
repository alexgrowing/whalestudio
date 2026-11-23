import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNormStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseSpanTensorOfDenseSubspacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInnerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationMultilinearNormSqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.RowEvalHH in
theorem GlobalTheory.RowEvalHH.conj_eval_mem_HH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c v₀ ht hLM hc hv S hS φ hφ
  classical
  obtain ⟨hDS, -, -, -, -, hloc⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  obtain ⟨hinj, hran⟩ := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
    X.B.e X.B.Re X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => (hDS v).2.2.2) (fun v => (X.low v).1) hloc X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens X.B.tens_spec

  let u : (∀ τ, ↥(Wsub R X c τ)) → X.B.Hs := fun y => tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))
  obtain ⟨f, K, hfe, hfn⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_multilinear_norm_sq R F X h hLev hGrp hMod t c ht S hS
  have hfi := GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner f K hfn
  have hgram : ∀ a b, ⟪evF R X h t c S a, evF R X h t c S b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ := by
    intro a b
    rw [← hfe a, ← hfe b, hfi a b, tensT_inner]
    rfl
  have hdense : Dense (Submodule.span ℂ (Set.range u) : Set X.B.Hs) :=
    GlobalTheory.T.dense_span_tensor_of_dense_subspaces' (tensT X) (Wsub R X c) (tensT_inner X) (tensT_dense X) (Wsub_dense R X c)
  obtain ⟨Aop, hA⟩ := GlobalTheory.T.exists_clm_of_gram_eq_smul' u (evF R X h t c S) K hgram hdense
  have hHom : Aop ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    intro g
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy1, hy2⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup R F X h hLev hGrp hMod hHost hιE t c ht hc S hS g y
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    change Aop (X.B.σs g (u y)) = X.B.R (g, 1) (Aop (u y))
    rw [← hy1]
    change Aop (u y') = _
    rw [hA, hA, hy2]
  have hRe : X.B.Re.comp Aop = Aop := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hA]
    exact GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  have heHom : Aop ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re :=
    Submodule.mem_map.2 ⟨Aop, hHom, hRe⟩

  let y₀ : ∀ τ, ↥(Wsub R X c τ) := fun τ => ⟨c τ (v₀ τ), Submodule.mem_map_of_mem (v₀ τ).2⟩
  have hu0 : u y₀ = X.B.tens X.B.w := by
    have : (fun τ => ((y₀ τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ))) = fun τ => X.B.w (X.pl.symm τ) := by
      funext τ
      exact hv τ
    change tensT X _ = _
    rw [this, tensT_w]
  have hvec : vecOf R X c y₀ = v₀ := by
    funext τ
    apply Subtype.ext
    exact (c τ).symm_apply_apply (v₀ τ)
  obtain ⟨c', -, hnorm⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  have hunit : ∀ τ, ‖((v₀ τ : (MP R).H τ))‖ = 1 := by
    intro τ
    rw [← (c τ).norm_map, hv τ]
    exact (X.low _).1
  obtain ⟨hmem, -, -⟩ := hnorm v₀ hunit S hS
  have hval : Aop (X.B.tens X.B.w) = star φ := by
    rw [← hu0, hA]
    unfold evF
    rw [hvec, dif_pos hmem]
    congr 1
    exact (Lp.ext (hφ.trans hmem.coeFn_toLp.symm)).symm
  have hmemHH : star φ ∈ Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund X.B.Re X.Rph := by
    rw [← hran]
    exact ⟨⟨Aop, heHom⟩, hval⟩
  exact hmemHH
