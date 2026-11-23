import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandTame

theorem integral_prod_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) (μ₄ : Measure δ) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure μ₃] [IsFiniteMeasure μ₄]
    (F : α × β × γ × δ → ℂ) (hF : Integrable F (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))) :
    ∫ y, F y ∂(μ₁.prod (μ₂.prod (μ₃.prod μ₄))) = ∫ a, ∫ b, ∫ c, ∫ d, F (a, b, c, d) ∂μ₄ ∂μ₃ ∂μ₂ ∂μ₁ := by
  rw [integral_prod _ hF]
  refine integral_congr_ae (hF.prod_right_ae.mono fun a ha => ?_)
  simp only
  rw [integral_prod _ ha]
  refine integral_congr_ae (ha.prod_right_ae.mono fun b hb => ?_)
  simp only
  rw [integral_prod _ hb]

theorem sfinite_of_finite {α : Type} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] : SFinite μ := inferInstance

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simp only [hh f hf]; exact h.cont f hf
  · simp only [hh f hf]; exact h.bdd f hf
  · simp only [hh f hf]; rw [e _ hI]; exact h.sup f hf m α hα hI

theorem rapid_core {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {G : GA D S → ℂ} (hG : RapidDec S G) (k : ℕ) :
    ∃ C : ℝ, ∀ n ∈ flagN d, ∀ h, ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D S S₀ ρ d
  obtain ⟨C', hC'⟩ := hG.decay (a * k)
  refine ⟨|C| ^ k * C', fun n hn h => ?_⟩
  have h1 : quotHeight S₀ h ≤ |C| * quotHeight S (n * d.emb0 h) ^ a :=
    (hC n hn h).1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖G (n * d.emb0 h)‖ * quotHeight S₀ h ^ k
      ≤ ‖G (n * d.emb0 h)‖ * (|C| * quotHeight S (n * d.emb0 h) ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (quotHeight_pos S₀ h).le h1 k) (norm_nonneg _)
    _ = |C| ^ k * (‖G (n * d.emb0 h)‖ * quotHeight S (n * d.emb0 h) ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * C' := mul_le_mul_of_nonneg_left (hC' _) (by positivity)

theorem rapid_theta {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} {χ χz : (AE D)ˣ →* Circle} {om : Om S L}
    (hom : IsWeilDatumO ψ S L χ χz om) {φ : GA D S → ℂ} (hφ : RapidDec S φ) {Φ₀ : WO S L → ℂ} (hΦ : IsThetaFunO ψ S L Φ₀)
    (k : ℕ) : ∃ C : ℝ, ∀ h v, ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k ≤ C := by
  obtain ⟨C, a, hC⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ S L χ χz om hom Φ₀ hΦ
  obtain ⟨C', hC'⟩ := hφ.decay (a + k)
  refine ⟨|C| * C', fun h v => ?_⟩
  have h1 : ‖om (h, 1) Φ₀ v‖ ≤ |C| * quotHeight S h ^ a := by
    have := hC h 1 v
    rw [quotHeight_of_mem L (one_mem _), mul_one] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_pos (quotHeight_pos S _) a).le)
  calc ‖φ h‖ * ‖om (h, 1) Φ₀ v‖ * quotHeight S h ^ k
      ≤ ‖φ h‖ * (|C| * quotHeight S h ^ a) * quotHeight S h ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (pow_pos (quotHeight_pos S _) k).le
    _ = |C| * (‖φ h‖ * quotHeight S h ^ (a + k)) := by ring
    _ ≤ |C| * C' := mul_le_mul_of_nonneg_left (hC' _) (abs_nonneg _)

theorem handP₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B),
    ∀ (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz →
    ∀ (φ : GA D J.W₀ → ℂ) (G : GA D B.V → ℂ) (Φ₀ : WO J.W₀ B.L → ℂ), RapidDec J.W₀ φ → RapidDec B.V G →
    IsThetaFunO ψ J.W₀ B.L Φ₀ → Tame ψ J.W₀ B.V₀ fun Ξ => B.per ψ (handP s vL omz φ Φ₀ Ξ) G := by
  intro D ψ σ J B s vL χ χz omz homz φ G Φ₀ hφ hG hΦ
  have hψ := homz.std
  haveI : ∀ V : HSp D, SecondCountableTopology (GA D V) := fun V => (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  haveI : ∀ V : HSp D, BorelSpace (GA D V) := fun V => ⟨rfl⟩
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.L.rank J.W₀.rank
  haveI : SecondCountableTopology (WO J.W₀ B.L) := i3
  haveI : BorelSpace (WO J.W₀ B.L) := ⟨rfl⟩
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A _ _ B.vA.haar B.vA.fund).ne
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ _ _ J.v0.haar J.v0.fund).ne
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) := isFiniteMeasure_restrict.2 (by rw [vL.covol.2.2]; exact ENNReal.one_ne_top)
  let Y : Type := GA D B.A × flagN B.d × GA D J.W₀ × WO J.W₀ B.L
  let m : Measure Y := (B.vA.μ.restrict B.vA.𝓕).prod ((B.vN.ν.restrict B.vN.𝓝).prod
    ((J.v0.μ.restrict J.v0.𝓕).prod (vL.μ.restrict vL.𝓕)))
  haveI : IsFiniteMeasure m := by dsimp only [m]; infer_instance
  haveI : SFinite m := sfinite_of_finite m
  let c : Y → ℂ := fun y => G (y.2.1.1 * embA B.d B.o y.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1) *
    (φ y.2.2.1 * star (omz (y.2.2.1, 1) Φ₀ y.2.2.2))
  have hn : Continuous fun y : Y => (y.2.1.1 : GA D B.V) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have h0 : Continuous fun y : Y => y.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hv : Continuous fun y : Y => y.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have he : Continuous fun y : Y => B.o.emb (y.1, 1) := B.o.continuous_emb.comp (continuous_fst.prodMk continuous_const)
  have hw : Continuous fun y : Y => (B.o.resT J.W₀).symm (0, y.2.2.2) :=
    (B.o.continuous_resT_symm J.W₀).comp (continuous_const.prodMk hv)
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V).2.2.2.2.1
  have hJ : Continuous fun p : (GA D J.W₀ × GA D B.L) × WO J.W₀ B.L => omz p.1 Φ₀ p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ _ _ χ χz omz homz Φ₀ hΦ
  have hc : Continuous c :=
    ((hG.continuous.comp (hn.mul (B.d.continuous_embed.comp he))).mul
      (continuous_star.comp ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 _).comp hn))).mul
      ((hφ.continuous.comp h0).mul (continuous_star.comp (hJ.comp ((h0.prodMk continuous_const).prodMk hv))))
  have hint : ∀ k : ℕ, Integrable
      (fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k) m := by
    intro k
    obtain ⟨C₁, h₁⟩ := rapid_core B.d hG k
    obtain ⟨C₂, h₂⟩ := rapid_theta homz hφ hΦ k
    have hcc : Continuous fun y : Y => ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k :=
      hc.norm.mul ((((continuous_quotHeight _).comp h0).mul ((continuous_quotHeight _).comp he)).pow k)
    refine Integrable.of_bound hcc.measurable.aestronglyMeasurable (C₁ * C₂) (.of_forall fun y => ?_)
    have p1 := quotHeight_pos J.W₀ y.2.2.1
    have p2 := quotHeight_pos B.V₀ (B.o.emb (y.1, 1))
    have n1 : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) y.2.1.1‖ = 1 := hψ.1.2.1 _
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := h₁ _ y.2.1.2 (B.o.emb (y.1, 1))
    have a2 := h₂ y.2.2.1 y.2.2.2
    calc ‖c y‖ * (quotHeight J.W₀ y.2.2.1 * quotHeight B.V₀ (B.o.emb (y.1, 1))) ^ k
        = (‖G (y.2.1.1 * B.d.emb0 (B.o.emb (y.1, 1)))‖ * quotHeight B.V₀ (B.o.emb (y.1, 1)) ^ k) *
          (‖φ y.2.2.1‖ * ‖omz (y.2.2.1, 1) Φ₀ y.2.2.2‖ * quotHeight J.W₀ y.2.2.1 ^ k) := by
          simp only [c, norm_mul, norm_star, n1, embA_apply, mul_pow]; ring
      _ ≤ C₁ * C₂ := mul_le_mul a1 a2 (by positivity) (le_trans (by positivity) a1)
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ Y m c (fun y => y.2.2.1) (fun y => B.o.emb (y.1, 1))
    (fun y => (B.o.resT J.W₀).symm (0, y.2.2.2)) hc.measurable h0 he hw hint
  refine tame_congr hψ hT fun f hf => ?_
  refine Eq.trans ?_ (integral_prod_four _ _ _ _ _ (hI f hf)).symm
  simp only [BesL.per, besPer, GlobalTheory.MixPer.besFun, handP, contractT, thPair]
  refine integral_congr_ae (.of_forall fun a => ?_)
  refine integral_congr_ae (.of_forall fun b => ?_)
  simp only
  rw [mul_assoc, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only
  rw [← integral_const_mul, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun v => ?_)
  simp only [c]
  ring

end GlobalTheory.HandTame

end
