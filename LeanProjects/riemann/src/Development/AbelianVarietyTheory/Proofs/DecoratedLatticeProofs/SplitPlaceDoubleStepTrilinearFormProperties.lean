import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinearStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGLStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AconvSingleList
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaTwoVarCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselThetaContractionExtendByZeroVacuumSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontriviaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

theorem isBiTheta_add' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ}
    (hf : IsBiTheta ψ A S A' f) (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem isBiTheta_zero' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem isBiTheta_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] (Λ : SB (X × Y) →ₗ[ℂ] (WO A S → WO S A' → ℂ))
    (h : ∀ a b, IsBiTheta ψ A S A' (Λ (GlobalTheory.LocFlat.CFac.prodSB a b))) (Ξ : SB (X × Y)) : IsBiTheta ψ A S A' (Λ Ξ) := by
  have hmem : Ξ ∈ Submodule.span ℂ (Set.range fun q : SB X × SB Y => GlobalTheory.LocFlat.CFac.prodSB q.1 q.2) := by
    rw [GlobalTheory.T.span_schwartzBruhatProduct_eq_top X Y]; trivial
  have key : ∀ c : ℂ, IsBiTheta ψ A S A' (Λ (c • Ξ)) := by
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      intro c
      have e : c • GlobalTheory.LocFlat.CFac.prodSB q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSB (c • q.1) q.2 := by
        change c • GlobalTheory.LocFlat.CFac.prodSBBil X Y q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSBBil X Y (c • q.1) q.2
        rw [map_smul, LinearMap.smul_apply]
      rw [e]; exact h _ _
    | zero => intro c; rw [smul_zero, map_zero]; exact isBiTheta_zero'
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact isBiTheta_add' (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  simpa using key 1

theorem tri : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ φ hφ
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hCL := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hν : Q.ν.IsAddHaarMeasure := Q.unitVol.1
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B Q.F.s Q.F.F₀ Q.F.G₀ Q.F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂ Q.F.bes'
  have hjac : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link (ofSplit Q.q) S.B S.B' S.l]; exact Q.F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _ (Q.c + 1 + 1)
    Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _ (Q.c + 1)
    Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac hC₂ Q.F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL Q.k (ofSplit Q.q) Q.ν hν ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL Q.F.s Q.F.s_ne
    _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hψkc : Continuous Q.ψk := by
    obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
    exact (hψk Q.ψk Q.char).1
  have hΛθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) := by
    haveI := GlobalTheory.SplitWeil.t2Space Q.k
    haveI : NonarchimedeanAddGroup Q.k := ⟨fun V hV => by
      obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
      exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
        GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
    haveI : TotallyDisconnectedSpace Q.k := inferInstance
    haveI : ∀ n n' : Type, T2Space (Matrix n n' Q.k) := fun n n' => inferInstanceAs (T2Space (n → n' → Q.k))
    haveI : ∀ n n' : Type, TotallyDisconnectedSpace (Matrix n n' Q.k) :=
      fun n n' => inferInstanceAs (TotallyDisconnectedSpace (n → n' → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₁ Q.n₀ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₁ → Q.n₀ → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₂ Q.n₁ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₂ → Q.n₁ → Q.k))
    refine isBiTheta_of_prod Λ fun Ξ₁ Ξ₂ => ?_
    obtain ⟨φ₀, φ₀', hφ₀⟩ := GlobalTheory.ContractionLocal.exists_normPair Q.ψk Q.ν hψkc hν Q.n₁
    obtain ⟨Ξ', h1, h2⟩ := hΛe (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁) (GlobalTheory.ContractionLocal.rowTens φ₀' Ξ₂)
    have e : Ξ' = GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂ :=
      Subtype.ext (funext fun q => by rw [h1, GlobalTheory.ContractionLocal.contr_tens, hφ₀, mul_one]; rfl)
    rw [← e, ← h2]
    exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hstd _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (hU₁.theta _) (hU₂.theta _)).1
  have hθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hstd _ _ _ _ (hΛθ Ξ) c₁ c₂
  obtain ⟨T, hT⟩ := GlobalTheory.T.doubleThetaLiftValue_bilinear D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ hΛθ
  have key : ∀ Ξ₁ Ξ₂ (f : GlobalTheory.TriStep.space Q), (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T Ξ₁ Ξ₂ f =
      GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f.1 := fun Ξ₁ Ξ₂ f => hT _ f
  refine ⟨GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.rep Q, (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T, GlobalTheory.TriStep.smooth Q,
    fun y f => rfl, GlobalTheory.T.mem_space_of_typed_automorphic D ψ σ S Q, ⟨fun Ψ₁ => ⟨fun Ψ₂ g hg v => ?_, fun g Ψ Ψ' v h => ?_⟩, fun g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ => ?_⟩,
    GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe T hT, fun Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f => ?_⟩
  · rw [key, key]
    exact GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ _ g hg v.1 v.2
  · rw [key, key]
    exact GlobalTheory.T.local_bimodel_translation D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ Ψ' h (hθ _) v.1 v.2
  · ext1 f
    rw [key, key]
    exact GlobalTheory.T.doubleThetaLiftValue_invariant_middleGL D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ (hθ _) f.1 f.2
  · rw [key]
    exact GlobalTheory.TriStep.valK_comb D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f.1 f.2

end GlobalTheory.TriStep
end
