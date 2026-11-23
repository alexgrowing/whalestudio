import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  have hT : IsMultMap θ M J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff D θ W S M J χ _).1 ((mem_multT θ M J χ F).1 hF)
  have hFv : ∀ x, F x = PiTensorProduct.lift (PiTensorProduct.lift.symm F) x := fun x => by
    rw [LinearEquiv.apply_symm_apply]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [hFv, LinearMap.map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut x), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp x)⟩
  | add a b ha hb =>
    rw [map_add]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add ha.1 hb.1,
      GlobalTheory.MultMem.isCuspFun_add ha.1.toIsAutFun hb.1.toIsAutFun ha.2 hb.2⟩

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, ?_⟩
    funext x
    simp [Lift.liftInt, thetaKO_zero]
  | add a b _ _ ha hb =>
    refine ⟨GlobalTheory.OrientedHeis.theta_add ha.1 hb.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    have h2 := congrFun hb.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 h2 ⊢
    simp only [thetaKO_add, add_mul]
    rw [integral_add (hI a ha.1 x) (hI b hb.1 x), h1, h2, add_zero]
  | smul c a _ ha =>
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c ha.1, ?_⟩
    funext x
    have h1 := congrFun ha.2 x
    simp only [Lift.liftInt, Pi.zero_apply] at h1 ⊢
    simp only [thetaKO_smul, mul_assoc]
    rw [integral_const_mul, h1, mul_zero]

theorem eq_zero_of_le_mul_pos {a K : ℝ≥0∞} (hK : K ≠ ∞) (h : ∀ δ : ℝ≥0∞, 0 < δ → a ≤ K * δ) : a = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  rcases eq_or_ne K 0 with rfl | hK0
  · exact (h 1 one_pos).trans (by simp)
  · have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
    have := h (ε / K) (ENNReal.div_pos hε' hK)
    rwa [ENNReal.mul_div_cancel hK0 hK] at this

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  obtain ⟨A, hA⟩ := hL.bound
  obtain ⟨d, hd⟩ := hA 0
  obtain ⟨C, hC⟩ := hd μ 𝓓 hμ h𝓓 U hU
  have hint : ∀ f', IsThetaFunO ψ V W f' → ∀ x,
      IntegrableOn (fun h => thetaKO ω x h f' * Φ h) 𝓕 ν := fun f' hf' x => by
    simpa [rTr] using hL.integ f' Φ hf' hΦ x 1
  have key : ∀ g ∈ GlobalTheory.Size.thetaLevel ψ V W U, Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 →
      growthSob θ V 0 A (lift ω ν 𝓕 f Φ) ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := by
    intro g hg hg0
    have hb := hC (f - g) (sub_mem hf hg) Φ hΦ
    have heq : lift ω ν 𝓕 (f - g) Φ = lift ω ν 𝓕 f Φ := by
      funext x
      have h0 := congrFun hg0 x
      simp only [lift, Lift.liftInt, Pi.zero_apply] at h0 ⊢
      simp only [thetaKO_sub, sub_mul]
      rw [integral_sub (hint f hf.1 x) (hint g hg.1 x), h0, sub_zero]
    rwa [heq] at hb
  have hdec := hL.decay_ne_top Φ hΦ A
  have hz : growthSob θ V 0 A (lift ω ν 𝓕 f Φ) = 0 := by
    refine eq_zero_of_le_mul_pos (K := C * decayInt ν 𝓕 A Φ) (ENNReal.mul_ne_top ENNReal.coe_ne_top hdec) ?_
    intro δ hδ
    obtain ⟨g, hg, hg0, hsm⟩ := happ d δ hδ
    calc growthSob θ V 0 A (lift ω ν 𝓕 f Φ)
        ≤ C * sobO ψ θ μ 𝓓 d (f - g) * decayInt ν 𝓕 A Φ := key g hg hg0
      _ ≤ C * δ * decayInt ν 𝓕 A Φ := by gcongr
      _ = C * decayInt ν 𝓕 A Φ * δ := by ring
  have hz' : growthSize V A (lift ω ν 𝓕 f Φ) = 0 := by simpa [growthSob] using hz
  unfold growthSize at hz'
  funext x
  have hx := ENNReal.ofReal_eq_zero.1 ((ENNReal.iSup_eq_zero.1 hz') x)
  have hpos : 0 < height V x ^ A := pow_pos (lt_of_lt_of_le one_pos ((height_laws V).1 x)) A
  rw [div_le_iff₀ hpos, zero_mul] at hx
  exact norm_le_zero_iff.1 hx

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
