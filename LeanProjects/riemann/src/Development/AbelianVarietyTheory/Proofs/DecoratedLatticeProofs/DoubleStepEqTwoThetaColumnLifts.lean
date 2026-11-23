import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumProductCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiContractedIsThetaFunEachVariaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.Contr

variable {D : D7}

theorem bdd_of_contAut {V : HSp D} (hV : CoCpt V) {φ : GA D V → ℂ} (hφ : IsContAut V φ) :
    ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨K, hK, hc⟩ := hV
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.2.continuousOn
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hc g
  rw [← hφ.1 γ hγ g]
  exact hC _ hk

theorem bdd_om_core {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {Ξ : WO B.V₀ J.W₀ → ℂ} (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (h₁ : GA D J.W₀) :
    ∃ C : ℝ, ∀ h₀ x, ‖s.om₀ (B.o.emb (h₀, 1), h₁) Ξ x‖ ≤ C := by
  obtain ⟨K, hK, hc⟩ := B.cpt
  have hcont : Continuous fun h₀ : GA D B.A => (B.o.emb (h₀, 1), h₁) :=
    (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const
  obtain ⟨c, hcb⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ _
    (hK.image hcont)
  refine ⟨c, fun h₀ x => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hc h₀
  have hγ' : B.o.emb (γ, 1) ∈ GQ B.V₀ := B.o.emb_mem_GQ hγ (one_mem _)
  have key := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ (B.o.emb (γ, 1)) hγ' 1 (one_mem _)
    (B.o.emb (h₀, 1)) h₁ (x ⬝ mt B.V₀ ((B.o.emb (γ, 1))⁻¹))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul, Matrix.mul_assoc, mt_inv_mul,
    Matrix.mul_one] at key
  rw [← key]
  exact hcb _ ⟨γ * h₀, hk, rfl⟩ _

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ')
    (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h1 : Continuous fun w : WO S L' => ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ w : Mx D B.L.rank S.rank) :=
    continuous_const.matrix_mul continuous_id
  have h2 : Continuous fun w : WO S L' => (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ w) : Mx D S.rank B.L.rank) :=
    continuous_adj.comp h1
  have h3 : Continuous fun w : WO S L' =>
      (giA S ⬝ (adj ((rat l.τ : Mx D B.L.rank L'.rank) ⬝ w) ⬝ gA B.L) : Mx D S.rank B.L.rank) :=
    continuous_const.matrix_mul (h2.matrix_mul continuous_const)
  exact h3.const_smul (incA D (-D.host.xi0⁻¹))

theorem continuous_core {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
    {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') {Ξ : WO B.V₀ J.W₀ → ℂ}
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (h₁ : GA D J.W₀) :
    Continuous fun p : WO J.W₀ L' × GA D B.A =>
      s.om₀ (B.o.emb (p.2, 1), h₁) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ p.1)) := by
  have hj := GlobalTheory.T.weilDatum_theta_jointlyContinuous D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ Ξ hΞ
  exact hj.comp (((B.o.continuous_emb.comp (continuous_snd.prodMk continuous_const)).prodMk continuous_const).prodMk
    ((B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk ((continuous_kappa l J.W₀).comp continuous_fst))))

end GlobalTheory.Unf.Contr

namespace GlobalTheory.Unf.Contr

variable {D : D7}

theorem exchange_gen {α β : Type} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [OpensMeasurableSpace β] [SecondCountableTopologyEither α β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (X₂ : α → ℂ) (φ : β → ℂ) (X₁ : β → α → ℂ)
    (hc : Continuous fun p : α × β => X₂ p.1 * (φ p.2 * X₁ p.2 p.1)) (C : ℝ)
    (hb : ∀ w h, ‖X₂ w * (φ h * X₁ h w)‖ ≤ C) :
    ∫ w, X₂ w * ∫ h, φ h * X₁ h w ∂ν ∂μ = ∫ h, φ h * ∫ w, X₂ w * X₁ h w ∂μ ∂ν := by
  have hint : Integrable (Function.uncurry fun w h => X₂ w * (φ h * X₁ h w)) (μ.prod ν) :=
    (integrable_const C).mono' hc.aestronglyMeasurable (ae_of_all _ fun p => hb p.1 p.2)
  calc ∫ w, X₂ w * ∫ h, φ h * X₁ h w ∂ν ∂μ = ∫ w, ∫ h, X₂ w * (φ h * X₁ h w) ∂ν ∂μ := by
        congr 1; funext w; rw [integral_const_mul]
    _ = ∫ h, ∫ w, X₂ w * (φ h * X₁ h w) ∂μ ∂ν := integral_integral_swap hint
    _ = ∫ h, φ h * ∫ w, X₂ w * X₁ h w ∂μ ∂ν := by
        congr 1; funext h; rw [← integral_const_mul]; congr 1; funext w; ring

theorem exchange {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)}
    {B' : BesLev D σ} (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ)
    (vL : VolM D B'.L.rank J.W₀.rank) {φ : GA D B.A → ℂ} {Ξ₁ : WO B.V₀ J.W₀ → ℂ} {Ξ₂ : WO J.W₀ B'.V₀ → ℂ}
    (hφ : IsContAut B.A φ) (hΞ₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁) (hΞ₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂)
    (h₁ : GA D J.W₀) (h₂ : GA D B'.A) :
    ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) *
        ∫ h₀ in B.vA.𝓕, φ h₀ * s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂B.vA.μ ∂vL.μ =
      ∫ h₀ in B.vA.𝓕, φ h₀ * ∫ w in vL.𝓕, s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) *
        s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)) ∂vL.μ ∂B.vA.μ := by
  obtain ⟨-, hsc, -, hbor, htg, -, hcount⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := hsc; haveI := hbor; haveI := htg; haveI := hcount
  haveI : BorelSpace (WO J.W₀ B'.L) := ⟨rfl⟩
  haveI := B.vA.haar
  have hfinA : B.vA.μ B.vA.𝓕 < ⊤ := by
    obtain ⟨K, hK, hc⟩ := B.cpt
    refine GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hK (fun g => ?_) B.vA.μ B.vA.fund
    obtain ⟨γ, hγ, hk⟩ := hc g
    exact ⟨γ⁻¹, inv_mem hγ, γ * g, hk, by rw [← mul_assoc, inv_mul_cancel, one_mul]⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfinA⟩
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  have hΨ₂ : IsThetaFunO ψ J.W₀ B'.V₀ (s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂) := s₂.weil₀.om_pres _ _ hΞ₂
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded s₂.weil₀.std hΨ₂
  obtain ⟨Cφ, hCφ⟩ := bdd_of_contAut B.cpt hφ
  obtain ⟨C₁, hC₁⟩ := bdd_om_core s₁ hΞ₁ h₁
  have cX₂ : Continuous fun w : WO J.W₀ B'.L => s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w)) :=
    hΨ₂.cont.comp ((B'.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk continuous_id))
  refine exchange_gen (vL.μ.restrict vL.𝓕) (B.vA.μ.restrict B.vA.𝓕)
    (fun w => s₂.om₀ (h₁, B'.o.emb (h₂, 1)) Ξ₂ ((B'.o.resT J.W₀).symm (0, w))) φ
    (fun h₀ w => s₁.om₀ (B.o.emb (h₀, 1), h₁) Ξ₁ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w)))
    ((cX₂.comp continuous_fst).mul ((hφ.2.comp continuous_snd).mul (continuous_core s₁ l hΞ₁ h₁)))
    (C₂ * (Cφ * C₁)) (fun w h₀ => ?_)
  rw [norm_mul, norm_mul]
  have a := hC₂ ((B'.o.resT J.W₀).symm (0, w))
  have b := hCφ h₀
  have c := hC₁ h₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))
  exact mul_le_mul a (mul_le_mul b c (norm_nonneg _) ((norm_nonneg _).trans b)) (by positivity)
    ((norm_nonneg _).trans a)

theorem contrLaw (D : D7) : ContrLaw D := by
  intro ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' φ Ξ₁ Ξ₂ hφ hΞ₁ hΞ₂
  have hth := GlobalTheory.T.besselFourierJacobi_contracted_isThetaFun_each_variable D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂
  refine ⟨hth.1, fun p => (hth.2 p).1, fun h₂ => ?_⟩
  unfold handFB pairKer contractT thPair handBF
  simp only [star_star]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₁ => ?_)
  simp only
  refine (exchange s₁ s₂ l vL hφ hΞ₁ hΞ₂ h₁ h₂).trans (integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_))
  simp only
  rw [GlobalTheory.T.weil_datum_product_compatibility D ψ σ B J B' s₁ s₂ l vL χA χA' χz oma omz omb omz' hV hW hoa hoz hob hoz' Ξ₁ Ξ₂ hΞ₁ hΞ₂ h₀ h₁ h₂]

end GlobalTheory.Unf.Contr
