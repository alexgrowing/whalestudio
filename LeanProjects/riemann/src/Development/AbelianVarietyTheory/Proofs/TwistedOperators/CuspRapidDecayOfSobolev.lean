import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace GlobalTheory.Mem.Lift GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth GlobalTheory.Chain.LiftConv
open scoped ENNReal NNReal Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.LiftReg

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
  {f f' : WO V W → ℂ} {F : GA D W → ℂ} {A d : ℕ}

theorem thetaKO_om (g g₀ : GA D V) (h h₀ : GA D W) (f : WO V W → ℂ) :
    thetaKO ω g h (ω (g₀, h₀) f) = thetaKO ω (g * g₀) (h * h₀) f := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem sobO_smul_measure (c : ℝ≥0) (μ : Measure (WO V W)) (𝓓 : Set (WO V W)) (d : ℕ) (f : WO V W → ℂ) :
    sobO ψ θ (c • μ) 𝓓 d f = (c ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) * sobO ψ θ μ 𝓓 d f := by
  simp only [sobO, wordSum, l2O, Measure.restrict_smul, eLpNorm_smul_measure_of_ne_top' ENNReal.ofNat_ne_top,
    Finset.mul_sum]
  rfl

theorem kernel_le (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ)
    {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ≥0, ∀ f ∈ thetaLevel ψ V W U, ∀ g h,
      ‖thetaKO ω g h f‖ ≤ C * (sobO ψ θ μ 𝓓 d f).toReal * height V g ^ A * quotHeight W h ^ A := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨C, hC0, hC⟩ := H.real ψ hθ hU
  obtain ⟨h0, h1⟩ := measure_dom hμ h𝓓
  lift μ 𝓓 to ℝ≥0 using h1 with m hm
  have hm0 : m ≠ 0 := by simpa using h0
  have hc : IsCovolOne (ratL W V) (m⁻¹ • μ) 𝓓 :=
    ⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hm0), h𝓓.mono Measure.smul_absolutelyContinuous, by
      rw [Measure.smul_apply, ← hm, ENNReal.smul_def, smul_eq_mul, ← ENNReal.coe_mul, inv_mul_cancel₀ hm0]; rfl⟩
  lift C to ℝ≥0 using hC0
  refine ⟨C * m⁻¹ ^ (2 : ℝ≥0∞).toReal⁻¹ * 2 ^ A, fun f hf g h => ?_⟩
  have h2 := (hC χS χT ω hω _ _ hc f hf).2 g
  rw [sobO_smul_measure, ENNReal.toReal_mul, ENNReal.coe_toReal] at h2
  refine (norm_le_quotHeight_pow (A := A) (thetaKO_left hω hf.1 g) (fun h => (h2 h).trans_eq (by
    rw [mul_pow, ← mul_assoc])) h).trans_eq ?_
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  ring

theorem growthSize_lift_le (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ)
    {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ≥0, ∀ f ∈ thetaLevel ψ V W U, ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (F : GA D W → ℂ),
      growthSize V A (lift ω ν 𝓕 f F) ≤ C * sobO ψ θ μ 𝓓 d f * decayInt ν 𝓕 A F := by
  obtain ⟨C, hC⟩ := kernel_le H hθ hω hμ h𝓓 hU
  refine ⟨C, fun f hf ν 𝓕 F => iSup_le fun g => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ h𝓓 hf.1 d
  have hg := pow_pos (height_pos V g) A
  rw [ENNReal.ofReal_div_of_pos hg, ofReal_norm_eq_enorm]
  refine ENNReal.div_le_of_le_mul ((enorm_integral_le_lintegral_enorm _).trans ?_)
  rw [mul_right_comm, decayInt, ← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)]
  refine lintegral_mono fun h => ?_
  rw [← ENNReal.ofReal_toReal hs, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm, norm_mul]
  exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (hC f hf g h) (norm_nonneg _)).trans_eq (by ring))

theorem integrand_le (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F) :
    ∃ C : ℝ, ∀ g h, ‖thetaKO ω g h f * F h‖ ≤ C * height V g ^ A := by
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓓, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, hC⟩ := kernel_le H hθ hω hμ.1 hμ.2.1 hU
  obtain ⟨B, hB⟩ := hF.decay A
  refine ⟨C * (sobO ψ θ μ 𝓓 d f).toReal * B, fun g h => ?_⟩
  have hg := pow_pos (height_pos V g) A
  rw [norm_mul, mul_right_comm]
  refine (mul_le_mul_of_nonneg_right (hC f hl g h) (norm_nonneg _)).trans ?_
  rw [mul_assoc, mul_comm _ ‖F h‖]
  exact mul_le_mul_of_nonneg_left (hB h) (by positivity)

theorem integrand_loc (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F) (g₀ : GA D V) :
    ∃ B : ℝ, ∀ᶠ g in 𝓝 g₀, ∀ h, ‖thetaKO ω g h f * F h‖ ≤ B := by
  obtain ⟨C, hC⟩ := integrand_le H hθ hω hf hF
  have hc : Continuous fun g => C * height V g ^ A := continuous_const.mul ((continuous_height V).pow A)
  exact ⟨_, (hc.continuousAt.eventually_lt continuousAt_const (lt_add_one _)).mono fun g hg h => (hC g h).trans hg.le⟩

theorem vol_ne_top (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) : ν 𝓕 ≠ ∞ :=
  (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W ν 𝓕 hν h𝓕).ne

theorem integrand_meas (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F) (g : GA D V) :
    AEStronglyMeasurable (fun h => thetaKO ω g h f * F h) (ν.restrict 𝓕) :=
  have : BorelSpace (GA D W) := ⟨rfl⟩
  ((thetaKO_continuous hω hf g).mul hF.continuous).measurable.aestronglyMeasurable

theorem continuous_lift (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F) :
    Continuous (lift ω ν 𝓕 f F) := by
  have : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 (vol_ne_top hν h𝓕)
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨B, hB⟩ := integrand_loc H hθ hω hf hF g₀
  exact continuousAt_of_dominated (bound := fun _ => B) (.of_forall (integrand_meas hω hf hF))
    (hB.mono fun h hh => .of_forall hh) (integrable_const B) (.of_forall fun h =>
      (((hω.om_cont f hf 0).comp (Continuous.prodMk_left h)).mul continuous_const).continuousAt)

theorem hasDerivAt_lift (hG : ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F)
    {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (g : GA D V) :
    HasDerivAt (fun t : ℝ => lift ω ν 𝓕 f F (g * oneP θ V τ X t)) (lift ω ν 𝓕 (dOmS θ ω τ X f) F g) 0 := by
  have : IsTopologicalGroup (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  have : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.2 (vol_ne_top hν h𝓕)
  obtain ⟨A, d, H⟩ := hG V.rank W.rank
  obtain ⟨ht, hd⟩ := tame_dOmS hθ hω hX
  have hf' : IsThetaFunO ψ V W (dOmS θ ω τ X f) := ht.theta hf
  obtain ⟨B, hB⟩ := integrand_loc (H V W rfl rfl) hθ hω hf' hF g
  have hco : Filter.Tendsto (fun t : ℝ => g * oneP θ V τ X t) (𝓝 0) (𝓝 g) := by
    have := (continuous_const (y := g).mul (continuous_oneP hθ hX)).tendsto 0
    rw [Pi.mul_apply, oneP_zero hθ, mul_one] at this
    exact this
  have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν.restrict 𝓕) (x₀ := (0 : ℝ))
    (F := fun t h => thetaKO ω (g * oneP θ V τ X t) h f * F h)
    (F' := fun t h => thetaKO ω (g * oneP θ V τ X t) h (dOmS θ ω τ X f) * F h)
    (bound := fun _ => B) (hco.eventually hB) (.of_forall fun t => integrand_meas hω hf hF _)
    (integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hF _) (integrand_meas hω hf' hF _)
    (.of_forall fun h t ht => ht h) (integrable_const B)
    (.of_forall fun h t _ => (hasDerivAt_oneP hθ hX (φ := fun g => thetaKO ω g h f)
      (φ' := fun g => thetaKO ω g h (dOmS θ ω τ X f))
      (fun g => by simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (g, h) 0) g t).mul_const (F h))).2
  simp only [oneP_zero hθ, mul_one] at this
  exact this

theorem lift_om (hω : IsWeilDatumO ψ V W χS χT ω) (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    (hf : IsThetaFunO ψ V W f) (hF : ∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) (g₀ : GA D V) (h₀ : GA D W) :
    lift ω ν 𝓕 (ω (g₀, h₀) f) (rTr W h₀ F) = rTr V g₀ (lift ω ν 𝓕 f F) := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν).1
  funext g
  simp only [lift, Lift.liftInt, rTr, thetaKO_om]
  exact GlobalTheory.Mem.IntByParts.setIntegral_mul_right (GQ W) ν h𝓕 (Φ := fun h => thetaKO ω (g * g₀) h f * F h)
    (fun γ hγ h => by simp only [thetaKO_left hω hf _ γ hγ, hF γ hγ]) h₀

theorem isAutFun_lift (H : KernelBound V W A d) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (hf : IsThetaFunO ψ V W f) (hF : RapidDec W F) :
    IsAutFun V (lift ω ν 𝓕 f F) := by
  refine ⟨fun γ hγ g => ?_, ?_, continuous_lift H hθ hω hν h𝓕 hf hF⟩
  · have e : ∀ h, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun h => by
      have := thetaKO_om (ω := ω) γ g 1 h f
      rw [one_mul] at this
      rw [← this]
      exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)
    simp only [lift, Lift.liftInt, e]
  · obtain ⟨U, U', hU, -, e⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D ψ hω.std V W ω (GlobalTheory.Ker.isWeak_of_datum hω)
      hω.om_cont f hf
    refine ⟨U, hU, fun k h1 h2 g => ?_⟩
    have := congrFun (lift_om hω hν h𝓕 hf hF.1 k 1) g
    rw [e k h1 h2 1 (one_mem _) (one_mem _), show rTr W 1 F = F from funext fun h => congrArg F (mul_one h)] at this
    exact this.symm

theorem lift_der_add (hG : ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (hf : IsThetaFunO ψ V W f) (hF : RapidDecSm θ W F)
    {τ : D.what₂.Tau} {Y : Matrix (Fin W.rank) (Fin W.rank) ℂ} (hY : Y ∈ lieAt W τ) (g : GA D V) :
    lift ω ν 𝓕 f (Rder θ W τ Y F) g + lift ω ν 𝓕 (dOmT θ ω τ Y f) F g = 0 := by
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D W ν hν).1
  obtain ⟨A, d, H⟩ := hG V.rank W.rank
  obtain ⟨ht, hd⟩ := tame_dOmT hθ hω hY
  have hf' : IsThetaFunO ψ V W (dOmT θ ω τ Y f) := ht.theta hf
  have h0 := hF.rapidDec
  have h1 := (hF.rder hY).rapidDec
  obtain ⟨B0, hB0⟩ := integrand_le (H V W rfl rfl) hθ hω hf h0
  obtain ⟨B1, hB1⟩ := integrand_le (H V W rfl rfl) hθ hω hf' h0
  obtain ⟨B2, hB2⟩ := integrand_le (H V W rfl rfl) hθ hω hf h1
  have key := GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ W) ν h𝓕 (vol_ne_top hν h𝓕)
    (Φ := fun h => thetaKO ω g h f * F h)
    (Φ' := fun h => thetaKO ω g h (dOmT θ ω τ Y f) * F h + thetaKO ω g h f * Rder θ W τ Y F h)
    (fun γ hγ h => by simp only [thetaKO_left hω hf _ γ hγ, h0.left hγ])
    ((thetaKO_continuous hω hf g).mul h0.continuous)
    (((thetaKO_continuous hω hf' g).mul h0.continuous).add ((thetaKO_continuous hω hf g).mul h1.continuous)) (hB0 g)
    (fun h => (norm_add_le _ _).trans (add_le_add (hB1 g h) (hB2 g h))) (oneP_zero (V := W) (τ := τ) (X := Y) hθ)
    fun h t => (hasDerivAt_oneP hθ hY (φ := fun h => thetaKO ω g h f) (φ' := fun h => thetaKO ω g h (dOmT θ ω τ Y f))
      (fun h => by simpa only [thetaKO, Prod.mk_mul_mk, mul_one] using hd f hf (g, h) 0) h t).mul
      (hasDerivAt_oneP hθ hY (hasDerivAt_Rder hF.smooth hY) h t)
  rw [integral_add (integrableOn_of_rapidDec hG hθ hω hf' hν h𝓕 h0 g)
    (integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 h1 g), add_comm] at key
  exact key

theorem lift_add_smul (hG : ThetaGrowth D) (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω)
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (hf : IsThetaFunO ψ V W f)
    (hf' : IsThetaFunO ψ V W f') (hF : RapidDec W F) (c : ℂ) :
    lift ω ν 𝓕 (f + c • f') F = lift ω ν 𝓕 f F + c • lift ω ν 𝓕 f' F := by
  funext g
  have := integral_add (integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 hF g)
    ((integrableOn_of_rapidDec hG hθ hω hf' hν h𝓕 hF g).const_mul c)
  rw [integral_const_mul] at this
  refine Eq.trans ?_ this
  simp only [lift, Lift.liftInt, thetaKO, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]

theorem growthSob_lift_le (hG : ThetaGrowth D) (H : KernelBound V W A d) (hθ : IsInfFam θ)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν) (k : ℕ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure) (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ)
    {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ≥0, ∀ f ∈ thetaLevel ψ V W U, ∀ F, RapidDec W F →
      growthSob θ V k A (lift ω ν 𝓕 f F) ≤ C * sobO ψ θ μ 𝓓 (d + k * 2) f * decayInt ν 𝓕 A F := by
  have hp := fun a : D.what₂.Tau × Fin V.rank × Fin V.rank =>
    GlobalTheory.SmoothAutCheck.parts_mem V a.1 (Matrix.single a.2.1 a.2.2 1)
  have ht := fun a => (tame_dOmS hθ hω (hp a).1).1.add hω.std hθ ((tame_dOmS hθ hω (hp a).2).1.smul Complex.I)
  choose c hc using fun l => (tame_word ht l).2
  obtain ⟨C, hC⟩ := growthSize_lift_le H hθ hω hμ h𝓓 hU
  refine ⟨C * ∑ n ∈ Finset.range (k + 1), ∑ a : Fin n → _, c (List.ofFn a), fun f hf F hF => ?_⟩
  simp only [growthSob, wordSum, ENNReal.coe_mul, ENNReal.coe_finset_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun a _ => ?_
  have e := (wordAct_rel (A := glDer θ V) (R := fun φ x => φ = lift ω ν 𝓕 x F ∧ IsThetaFunO ψ V W x) (List.ofFn a)
    (fun i _ φ x h => ⟨by
      have h1 : IsThetaFunO ψ V W _ := (tame_dOmS hθ hω (hp i).1).1.theta h.2
      have h2 : IsThetaFunO ψ V W _ := (tame_dOmS hθ hω (hp i).2).1.theta h.2
      rw [h.1]
      refine Eq.trans ?_ (lift_add_smul hG hθ hω hν h𝓕 h1 h2 hF _).symm
      exact congrArg₂ (fun a b => a + Complex.I • b)
        (funext fun g => (hasDerivAt_lift hG hθ hω hν h𝓕 h.2 hF (hp i).1 g).deriv)
        (funext fun g => (hasDerivAt_lift hG hθ hω hν h𝓕 h.2 hF (hp i).2 g).deriv), (ht i).theta h.2⟩) ⟨rfl, hf.1⟩).1
  rw [e]
  refine (hC _ ((tame_word ht _).1 U f hf) ν 𝓕 F).trans (mul_le_mul' ?_ le_rfl)
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ((hc _ μ 𝓓 d f hf.1).trans (mul_le_mul' le_rfl (sobO_mono ?_)))
  have := Finset.mem_range.1 hn
  rw [List.length_ofFn]
  omega

theorem liftPropsRapid_of_growth (D : D7) (hG : ThetaGrowth D) : LiftPropsRapid D := by
  intro V W θ ψ χS χT ω hθ hω ν 𝓕 hν h𝓕
  obtain ⟨A, d, H⟩ := hG V.rank W.rank
  replace H := H V W rfl rfl
  have hdec : ∀ F, RapidDecSm θ W F → ∀ A, decayInt ν 𝓕 A F ≠ ∞ := fun F hF A =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ((rapidDec_iff_decaySize.1 hF.rapidDec).2.2 A) (vol_ne_top hν h𝓕))
      (decayInt_le ν 𝓕 A F)
  have hsm : ∀ f F, IsThetaFunO ψ V W f → RapidDecSm θ W F → lift ω ν 𝓕 f F ∈ SmFun θ V := fun f F hf hF => by
    refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ V {φ | ∃ f, IsThetaFunO ψ V W f ∧ φ = lift ω ν 𝓕 f F} ?_ ?_ _
      ⟨f, hf, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact continuous_lift H hθ hω hν h𝓕 hf hF.rapidDec
    · rintro _ ⟨f, hf, rfl⟩ τ X hX
      exact ⟨_, ⟨_, (tame_dOmS hθ hω hX).1.theta hf, rfl⟩, hasDerivAt_lift hG hθ hω hν h𝓕 hf hF.rapidDec hX⟩
  refine
    { integ := fun f F hf hF g h₀ => integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 (hF.rapidDec.mul_right h₀) g
      integ_der := fun f F hf hF τ Y hY g => integrableOn_of_rapidDec hG hθ hω hf hν h𝓕 (hF.rder hY).rapidDec g
      aut := fun f F hf hF => isAutFun_lift H hθ hω hν h𝓕 hf hF.rapidDec
      equiv := fun f F hf hF => lift_om hω hν h𝓕 hf hF.left
      smooth := hsm
      dS := fun f hf τ X hX => ⟨(tame_dOmS hθ hω hX).1.theta hf, fun z => by
        simpa only [one_mul, map_one, Module.End.one_apply] using (tame_dOmS hθ hω hX).2 f hf 1 z⟩
      dT := fun f hf τ Y hY => ⟨(tame_dOmT hθ hω hY).1.theta hf, fun z => by
        simpa only [one_mul, map_one, Module.End.one_apply] using (tame_dOmT hθ hω hY).2 f hf 1 z⟩
      derS := fun f F hf hF τ X hX => funext fun g => (hasDerivAt_lift hG hθ hω hν h𝓕 hf hF.rapidDec hX g).deriv
      derT := fun f F hf hF τ Y hY g => ?_
      growth := fun f F hf hF => ?_
      decay_ne_top := hdec
      bound := ⟨A, fun k => ⟨d + k * 2, fun μ 𝓓 hμ h𝓓 U hU =>
        (growthSob_lift_le hG H hθ hω hν h𝓕 k hμ h𝓓 hU).imp fun C hC f hf F hF => hC f hf F hF.rapidDec⟩⟩ }
  · simp only [lift_om hω hν h𝓕 hf hF.left, lift_der_add hG hθ hω hν h𝓕 hf hF hY g]
    exact hasDerivAt_const _ _
  · obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
    obtain ⟨μ, 𝓓, hμ⟩ := exists_isCovolOne V W
    refine unifModGrowth_iff.2 ⟨A, growthSize_rWord_ne_top hθ (hsm f F hf hF) fun k => ?_⟩
    obtain ⟨C, hC⟩ := growthSob_lift_le hG H hθ hω hν h𝓕 k hμ.1 hμ.2.1 hU
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf _)) (hdec F hF A)) (hC f hl F hF.rapidDec)

theorem cuspRapidDecay_of_sobolev (hP : GlobalTheory.Published.CuspDecaySobolev) : GlobalTheory.Published.CuspRapidDecay := by
  intro D θ hθ V e he φ ha hs hg hc
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain rfl := GlobalTheory.SmoothForms.eq_expInf R he
  exact ((rapidDec_iff_isRapidDecay hθ).1 (rapidDec_of_cuspDecaySobolev hP hθ ha
    ((GlobalTheory.SmoothForms.smooth_iff R φ).2 hs) (unifModGrowth_of_isUnifModerate hθ hg) hc)).2.2

theorem liftProps_of_rapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hG : ThetaGrowth D) : LiftProps D :=
  liftProps_of_rapid hP (liftPropsRapid_of_growth D hG)

theorem liftProps_of_growth (hP : GlobalTheory.Published.CuspDecaySobolev) (D : D7) (hG : ThetaGrowth D) : LiftProps D :=
  liftProps_of_rapidDecay (cuspRapidDecay_of_sobolev hP) D hG

end GlobalTheory.Chain.LiftReg

end
