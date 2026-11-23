import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleOrthogonalSumSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTensorRuleTargetOrthogonalSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepCommutesSliceSuperpositionTargetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLineStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineLinkGramSimilitudeBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ContrKernel

variable {D : D7}

theorem continuous_ofAdj (S T : HSp D) : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj S T) := by
  have h : Continuous fun z : Mx D S.rank T.rank => giA T ⬝ (adj z ⬝ gA S) :=
    continuous_const.matrix_mul
      ((GlobalTheory.MixModel.continuous_adj (D := D) (m := S.rank) (n := T.rank)).matrix_mul continuous_const)
  exact h.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) :=
  (continuous_ofAdj B.L S).comp (continuous_const.matrix_mul continuous_id)

theorem integrable_of_cont_bdd {m n : ℕ} (μ : Measure (Mx D m n)) [IsFiniteMeasure μ] (f : Mx D m n → ℂ)
    (hc : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := hb
  exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem symm_resS_symm {S A B : HSp D} (o : OrthDec S A B) (T : HSp D) (u : WO B T) (v : WO A T) :
    (o.symm.resS T).symm (u, v) = (o.resS T).symm (v, u) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply, add_comm]; rfl

theorem symm_resT_symm {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u : WO S B) (v : WO S A) :
    (o.symm.resT S).symm (u, v) = (o.resT S).symm (v, u) := by
  rw [OrthDec.resT_symm_apply, OrthDec.resT_symm_apply, add_comm]; rfl

theorem kernel_doubleStep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (χA χA' χz : ((AE D)ˣ →* Circle)) (oma : Om B.A J.W₀) (omz : Om B.L J.W₀) (omb : Om J.W₀ B'.A) (omz' : Om J.W₀ B'.L), s₁.χV = χA * χz → s₂.χW = χA' * χz → IsWeilDatumO ψ B.A J.W₀ χA s₁.χW oma → IsWeilDatumO ψ B.L J.W₀ χz s₁.χW omz → IsWeilDatumO ψ J.W₀ B'.A s₂.χV χA' omb → IsWeilDatumO ψ J.W₀ B'.L s₂.χV χz omz' → ∀ (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ₁ → IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂ → ∀ h₀ h₁ h₂, ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ = omb (h₁, h₂) (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) 0 := by
  intro D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂
  have hstd : IsStdChar D ψ (-1) := hoa.std
  have TS := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hstd B.V₀ B.A B.L B.o J.W₀
  have TT := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hstd B'.V₀ B'.A B'.L B'.o J.W₀
  have hw₁ : IsWeilDatumO ψ B.V₀ J.W₀ (χA * χz) s₁.χW s₁.om₀ := hV ▸ s₁.weil₀
  have hw₂ : IsWeilDatumO ψ J.W₀ B'.V₀ s₂.χV (χA' * χz) s₂.om₀ := hW ▸ s₂.weil₀
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI : BorelSpace (WO B.L J.W₀) := ⟨rfl⟩

  have hS₁ : ∀ u, IsThetaFunO ψ B.L J.W₀ fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z)) := (TS.slice_theta Ξ₁ hΞ₁).2
  have hS₂ : ∀ v, IsThetaFunO ψ J.W₀ B'.L fun w => Ξ₂ ((B'.o.resT J.W₀).symm (v, w)) := (TT.slice_theta Ξ₂ hΞ₂).2

  obtain ⟨Hf, hHf⟩ : ∃ Hf : WO B.A J.W₀ → WO B.L J.W₀ → ℂ,
      Hf = fun u z => omz (1, h₁) (fun z' => Ξ₁ ((B.o.resS J.W₀).symm (u, z'))) z := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ Gf : WO J.W₀ B'.A → WO J.W₀ B'.L → ℂ,
      Gf = fun v w => omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) w := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁d⟩ : ∃ F₁ : WO B.V₀ J.W₀ → ℂ, F₁ = fun x => Hf (B.o.resS J.W₀ x).1 (B.o.resS J.W₀ x).2 := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂d⟩ : ∃ F₂ : WO J.W₀ B'.V₀ → ℂ, F₂ = fun x => Gf (B'.o.resT J.W₀ x).1 (B'.o.resT J.W₀ x).2 :=
    ⟨_, rfl⟩
  have hF₁s : ∀ u z, F₁ ((B.o.resS J.W₀).symm (u, z)) = Hf u z := by
    intro u z; rw [hF₁d]; simp only [AddEquiv.apply_symm_apply]
  have hF₂s : ∀ v w, F₂ ((B'.o.resT J.W₀).symm (v, w)) = Gf v w := by
    intro v w; rw [hF₂d]; simp only [AddEquiv.apply_symm_apply]

  have hF₁ : IsThetaFunO ψ B.V₀ J.W₀ F₁ := by
    have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.L B.A J.W₀ B.o.symm χz s₁.χW omz hoz Ξ₁ hΞ₁ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (1, h₁)).1
    have e : F₁ = fun x => omz (1, h₁) (fun u => Ξ₁ ((B.o.symm.resS J.W₀).symm (u, (B.o.symm.resS J.W₀ x).2)))
        (B.o.symm.resS J.W₀ x).1 := by
      funext x; rw [hF₁d, hHf]; simp only [symm_resS_symm]; rfl
    rw [e]; exact h
  have hF₂ : IsThetaFunO ψ J.W₀ B'.V₀ F₂ := by
    have h := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.L B'.A J.W₀ B'.o.symm s₂.χV χz omz' hoz' Ξ₂ hΞ₂ Unit 0 (fun _ => 0) (fun _ => 0)
      measurable_const (integrable_zero _ _ _) (h₁, 1)).1
    have e : F₂ = fun x => omz' (h₁, 1) (fun u => Ξ₂ ((B'.o.symm.resT J.W₀).symm (u, (B'.o.symm.resT J.W₀ x).2)))
        (B'.o.symm.resT J.W₀ x).1 := by
      funext x; rw [hF₂d, hGf]; simp only [symm_resT_symm]; rfl
    rw [e]; exact h

  obtain ⟨b₁, hb₁d⟩ : ∃ b₁ : WO J.W₀ B'.L → ℂ, b₁ = fun w => oma (h₀, h₁) (fun u => Hf u (l.κ J.W₀ w)) 0 := ⟨_, rfl⟩
  have hA : ∀ w, s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) = b₁ w := by
    intro w
    rw [(TS.om_slice χA χz s₁.χW s₁.om₀ oma omz hw₁ hoa hoz h₀ 1 h₁ Ξ₁ hΞ₁ (l.κ J.W₀ w)).2 0, hb₁d, hHf]
  have hB : ∀ w, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) = omb (h₁, h₂) (fun v => Gf v w) 0 := by
    intro w
    rw [(TT.om_slice s₂.χV χA' χz s₂.om₀ omb omz' hw₂ hob hoz' h₁ h₂ 1 Ξ₂ hΞ₂ w).2 0, hGf]

  have hb₁int : Integrable b₁ (vL.μ.restrict vL.𝓕) := by
    have th := hw₁.om_pres (B.o.emb (h₀, 1), h₁) Ξ₁ hΞ₁
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded B.V₀ J.W₀ ψ hstd _ th
    have e : b₁ = fun w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) :=
      funext fun w => (hA w).symm
    rw [e]
    exact integrable_of_cont_bdd _ _ (th.cont.comp ((B.o.continuous_resS_symm J.W₀).comp
      (continuous_const.prodMk (continuous_kappa l J.W₀)))) ⟨C, fun w => hC _⟩
  have hGint : ∀ v, Integrable (Gf v) (vL.μ.restrict vL.𝓕) := by
    intro v
    have th := hoz'.om_pres (h₁, 1) _ (hS₂ v)
    obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded J.W₀ B'.L ψ hstd _ th
    have e : Gf v = omz' (h₁, 1) (fun w' => Ξ₂ ((B'.o.resT J.W₀).symm (v, w'))) := by rw [hGf]
    rw [e]
    exact integrable_of_cont_bdd _ _ th.cont ⟨C, hC⟩

  have hLine : ∀ u v, ∫ w, Gf v w * Hf u (l.κ J.W₀ w) ∂(vL.μ.restrict vL.𝓕) = contr l J.W₀ vL Ξ₁ Ξ₂ u v := by
    intro u v
    have hrank : B.L.rank = B'.L.rank := B.line.1.trans B'.line.1.symm
    have hgram := (GlobalTheory.T.besselLineLink_gram_similitude_bijective D (σ + 1) B B'.L B'.ζ B'.line l).1
    have CL := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ B.L B'.L J.W₀ l.τ hrank hgram χz s₁.χW s₂.χV omz omz' hoz hoz'
      (fun z => Ξ₁ ((B.o.resS J.W₀).symm (u, z))) (hS₁ u)
    have CU := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ J.W₀ B'.L s₂.χV χz omz' hoz' vL (h₁, 1) _ _ (hS₂ v) CL.1
    rw [CL.2 h₁] at CU
    simp only [thPair, star_star] at CU
    rw [hGf, hHf]
    exact CU

  have hInner : ∀ v, oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0 =
      ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := by
    intro v
    have e : (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) =
        fun u => ∫ w, Gf v w * F₁ ((B.o.resS J.W₀).symm (u, l.κ J.W₀ w)) ∂(vL.μ.restrict vL.𝓕) := by
      funext u; rw [← hLine u v]; simp only [hF₁s]
    rw [e, (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ B.V₀ B.A B.L J.W₀ B.o χA s₁.χW oma hoa F₁ hF₁ (WO J.W₀ B'.L) (vL.μ.restrict vL.𝓕)
      (l.κ J.W₀) (Gf v) (continuous_kappa l J.W₀).measurable (hGint v) (h₀, h₁)).2 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF₁s, hF₂s, id, hb₁d]
    exact mul_comm _ _
  have hOuter := (GlobalTheory.T.weilRep_commutes_slice_superposition_target D ψ B'.V₀ B'.A B'.L J.W₀ B'.o s₂.χV χA' omb hob F₂ hF₂ (WO J.W₀ B'.L)
    (vL.μ.restrict vL.𝓕) id b₁ measurable_id hb₁int (h₁, h₂)).2 0
  have e : (fun v => oma (h₀, h₁) (fun u => contr l J.W₀ vL Ξ₁ Ξ₂ u v) 0) =
      fun v => ∫ w, b₁ w * F₂ ((B'.o.resT J.W₀).symm (v, id w)) ∂(vL.μ.restrict vL.𝓕) := funext hInner
  rw [e, hOuter]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [hA, hB, hF₂s, id]
  exact mul_comm _ _

end GlobalTheory.ContrKernel

end
