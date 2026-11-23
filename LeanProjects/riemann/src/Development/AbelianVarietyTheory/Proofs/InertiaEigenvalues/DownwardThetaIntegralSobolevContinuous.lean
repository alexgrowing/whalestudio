import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.DownLift.Sobolev₂

open GlobalTheory.Size GlobalTheory.Grow
open scoped ComplexOrder

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem integrableOn_extV (R : RealDat D A Ks) (hm : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hc := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hK := hc.choose_spec.1
  have hKc := hc.choose_spec.2
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hFc : Continuous (R.extV i t y) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hlc : Continuous fun h => l (R.extV i t y h) := l.continuous_of_finiteDimensional.comp hFc
  have hH : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have : IsFiniteMeasure ((R.νV i t).restrict (R.fdV i t)) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Vc D i) (R.νV i t) (R.fdV i t)
      hH hfd).ne
  have hb := hK.exists_bound_of_continuousOn hlc.continuousOn
  have hbd : ∀ h, ‖l (R.extV i t y h)‖ ≤ hb.choose := by
    intro h
    obtain ⟨γ, hγ, c, hc, e⟩ := hKc h
    rw [e, hFi γ hγ c]
    exact hb.choose_spec c hc
  exact Integrable.of_bound hlc.aestronglyMeasurable hb.choose (.of_forall hbd)

set_option maxHeartbeats 1000000 in

theorem downInt_sobolev_cont : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y μ 𝓕 hμ f hf l g ε hε
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hG.core.thP.ωP i t
  have hψ := hω.std
  have hpt := hG.core.thP.pt_theta i t
  have hvP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hpt 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  obtain ⟨U₀, hU₀, hl₀⟩ := isTheta_iff_level.1 hvP
  obtain ⟨U₁, hU₁, hl₁⟩ := isTheta_iff_level.1 hf
  have hUo : IsOpen ((U₁ ⊓ U₀ : AddSubgroup (WO (Vc D i) (Wc D i))) : Set (WO (Vc D i) (Wc D i))) := by
    rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₀
  have hptl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) U₀ := fun P =>
    ⟨hpt P, fun u hu h0 => by
      have e := ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hψ hθ _ hvP).2 u h0).2
      unfold RealDat.ptP
      rw [← e, hl₀.2 u hu h0]⟩
  have hfl : f ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := thetaLevel_anti inf_le_left hl₁
  have hpl : ∀ P, R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P =>
    thetaLevel_anti inf_le_right (hptl P)
  have hml : ∀ P, f - R.ptP i t P ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P => sub_mem hfl (hpl P)
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (Vc D i).rank (Wc D i).rank
  obtain ⟨C, hC0, hC⟩ := (H (Vc D i) (Wc D i) rfl rfl).real R.ψ hθ hUo
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  obtain ⟨HK, hHK⟩ := hK.exists_bound_of_continuousOn (continuous_height (Vc D i)).continuousOn
  have hHK0 : 0 ≤ HK := by
    obtain ⟨γ, -, c, hc, -⟩ := hKc 1
    exact (norm_nonneg _).trans (hHK c hc)
  have hg0 := height_pos (Wc D i) g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (HK * height (Wc D i) g) ^ Ae := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ by positivity
  have hbound : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀), ∀ h,
      ‖thetaKO (R.ωP i t) h g φ‖ ≤ B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by
    intro φ hφ h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hKc h
    rw [GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hφ.1 γ hγ c g]
    have h1 := (hC _ _ (R.ωP i t) hω μ 𝓕 hμ φ hφ).2 c g
    have hc1 : height (Vc D i) c ≤ HK := (Real.le_norm_self _).trans (hHK c hc)
    have hc0 := height_pos (Vc D i) c
    have hs : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d φ).toReal := ENNReal.toReal_nonneg
    have h2 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (height (Vc D i) c * height (Wc D i) g) ^ Ae ≤
        C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc0 hg0).le
        (mul_le_mul_of_nonneg_right hc1 hg0.le) Ae) (mul_nonneg hC0 hs)
    have h3 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae =
        B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by rw [hB]; ring
    exact h1.trans (h2.trans_eq h3)
  have hl1 : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := integrableOn_extV R hm i t y l
  have hint : ∀ φ ∈ thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀),
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g φ * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := fun φ hφ =>
    Integrable.bdd_mul hl1 ((hω.om_cont φ hφ.1 0).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (.of_forall (hbound φ hφ))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ h in R.fdV i t, ‖l (R.extV i t y h)‖ ∂(R.νV i t) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < B * M + 1 := by positivity
  refine ⟨d, ENNReal.ofReal (ε / (B * M + 1)), ENNReal.ofReal_pos.2 (by positivity), fun P hP => ?_⟩
  have hs := ENNReal.toReal_lt_of_lt_ofReal hP
  have hs0 : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := ENNReal.toReal_nonneg
  have e : downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g =
      ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h) ∂(R.νV i t) := by
    have i1 := hint f hfl
    have i2 := hint (R.ptP i t P) (hpl P)
    have e1 := integral_sub i1 i2
    refine e1.symm.trans (integral_congr_ae (.of_forall fun h => ?_))
    have e2 : R.ωP i t (h, g) (f - R.ptP i t P) = R.ωP i t (h, g) f - R.ωP i t (h, g) (R.ptP i t P) :=
      LinearMap.map_sub _ _ _
    show thetaKO (R.ωP i t) h g f * l (R.extV i t y h) - thetaKO (R.ωP i t) h g (R.ptP i t P) * l (R.extV i t y h) =
      thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h)
    refine (sub_mul _ _ _).symm.trans (congrArg (· * l (R.extV i t y h)) ?_)
    exact (congrFun e2 0).symm
  rw [e]
  have hle := norm_integral_le_of_norm_le (μ := (R.νV i t).restrict (R.fdV i t))
    (f := fun h => thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h))
    (hl1.norm.const_mul (B * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal))
    (.of_forall fun h => by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound _ (hml P) h) (norm_nonneg _)))
  rw [integral_const_mul, ← hMdef] at hle
  calc _ ≤ _ := hle
    _ ≤ (B * M + 1) * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := by nlinarith
    _ < (B * M + 1) * (ε / (B * M + 1)) := by gcongr
    _ = ε := by field_simp

end GlobalTheory.DownLift.Sobolev₂
