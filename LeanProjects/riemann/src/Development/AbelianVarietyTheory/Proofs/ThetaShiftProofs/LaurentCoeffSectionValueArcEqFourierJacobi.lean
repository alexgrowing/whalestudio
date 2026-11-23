import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ConjugateConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExponentialDerivativeAtZeroIsTangent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoeffEqZeroOfHasSumZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcNilpotent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPointStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2OfAnalyticGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianPartSectionNormSqEqThetaDataStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermFormSumSmul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFrBor
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NfacParallelFlowV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstRatioOfNormEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FreqRealNonnegIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockTypeStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcCoeff

theorem norm_eTwoPi_zpow (w : ℂ) (m : ℤ) : ‖eTwoPi w ^ m‖ = Real.exp (-(2 * Real.pi * m) * w.im) := by
  unfold eTwoPi
  rw [← Complex.exp_int_mul, Complex.norm_exp]
  congr 1
  simp
  ring

theorem differentiableOn_of_hasSum (a : ℤ → ℂ) (T : ℝ) (f : ℂ → ℂ)
    (h : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m) (f w)) :
    DifferentiableOn ℂ f {w | T < w.im} := by
  intro w₀ hw₀
  have hw₀' : T < w₀.im := hw₀
  set y₁ : ℝ := (T + w₀.im) / 2 with hy₁
  set y₂ : ℝ := w₀.im + 1 with hy₂
  have hs : ∀ y : ℝ, T < y → Summable fun m : ℤ => ‖a m‖ * Real.exp (-(2 * Real.pi * m) * y) := fun y hy => by
    have := (h (y * Complex.I) (by simpa using hy)).summable.norm
    simpa only [norm_mul, norm_eTwoPi_zpow, Complex.mul_I_im, Complex.ofReal_re] using this
  have hO : IsOpen {w : ℂ | y₁ < w.im ∧ w.im < y₂} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hd : DifferentiableOn ℂ (fun w => ∑' m : ℤ, a m * eTwoPi w ^ m) {w : ℂ | y₁ < w.im ∧ w.im < y₂} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((hs y₁ (by linarith)).add (hs y₂ (by linarith))) (fun m => ?_) hO (fun m w hw => ?_)
    · have : (fun w => a m * eTwoPi w ^ m) = fun w => a m * Complex.exp (m * (2 * Real.pi * Complex.I * w)) := by
        funext w
        rw [Complex.exp_int_mul]
        rfl
      rw [this]
      fun_prop
    · rw [norm_mul, norm_eTwoPi_zpow, ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rcases le_total 0 (2 * Real.pi * m) with hm | hm
      · exact le_add_of_le_of_nonneg (Real.exp_le_exp.2 (by nlinarith [hw.1])) (Real.exp_pos _).le
      · exact le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 (by nlinarith [hw.2]))
  have hm : {w : ℂ | y₁ < w.im ∧ w.im < y₂} ∈ nhds w₀ := hO.mem_nhds ⟨by linarith, by linarith⟩
  refine ((hd.differentiableAt hm).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hm] with w hw
  exact (h w (by linarith [hw.1])).tsum_eq.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem two_sum_eq_trace (X : Data E r) {ν s : E} (hν : cc ν = ν) (hs : cc s = s) :
    2 * ∑ τ : X.Ψ, (τ.1 ν).re * (τ.1 s).re = ((Algebra.trace ℚ E (ν * s) : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, X.trace_eq_Psi]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, RealEmbeddingCharacters.emb_real hs, RealEmbeddingCharacters.emb_real hν, map_mul, Complex.conj_ofReal, Complex.conj_ofReal,
    Complex.ofReal_re, Complex.ofReal_re]
  ring

theorem coeff_eq_of_betaAt (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P)
    {ξ' : Fin r → E} (hξ : X.IsIso ξ') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ξ : Module.Dual ℤ M) (N : ℕ) (be : LinearMap.BilinForm ℤ M)
    (hbe : ∀ y z, (N : ℤ) ∣ be y z) {ν₀ sE : E} {jj : ℤ} (hβ : BetaAt ξ N be ν₀ jj) (hs : IsBePar ξ be sE)
    (hpos : ∀ τ : X.Ψ, 0 < (τ.1 sE).re) (hT : TransvIn X N la)
    (hlev : ∀ s : E, LevelPar ξ N s → ∀ v ∈ X.Λ, ∃ u ∈ X.Λ,
      (transvMat X.Gm ξ' (s * X.κ0)).mulVec v - v = (N : E) • u)
    (κ w₁ : ℂ) (a : ℤ → ℂ) (T : ℝ)
    (ha : ∀ w : ℂ, T < w.im → HasSum (fun m : ℤ => a m * eTwoPi w ^ m)
      (κ * P (X.flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x))) :
    a jj * eTwoPi w₁ ^ jj = κ * X.fj la ξ' (fun τ => (τ.1 ν₀).re) P x := by
  obtain ⟨hν₀, hβ⟩ := hβ
  obtain ⟨htr, huq⟩ := hβ sE hs
  have hsL : LevelPar ξ N sE := ⟨hs.1, fun y z => by
    obtain ⟨m, hm⟩ := hbe y z
    exact ⟨m, by rw [hs.2, hm]; push_cast; rfl⟩⟩
  have hfr : ∀ ν : X.Ψ → ℝ, X.fj la ξ' ν P x ≠ 0 → ∃ ν₁ : E, cc ν₁ = ν₁ ∧ (ν = fun τ => (τ.1 ν₁).re) ∧
      (∀ τ : E →+* ℂ, 0 ≤ (τ ν₁).re) ∧ ∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν₁ * s) = m := by
    intro ν hν
    obtain ⟨ν₁, h1, h2, h3, h4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r X la P hP ξ' hξ ν x hx hν
    exact ⟨ν₁, h1, funext h2, h3, fun s hs' => h4 s hs'.1 (hT ξ' hξ s hs'.1 (hlev s hs'))⟩
  refine GlobalTheory.LaurentFJ.coeff_mul_zpow_eq_mul_fj X hP.1 hξ hx (fun τ => (τ.1 sE).re) (fun τ => (hpos τ).le) _ jj
    ?_ (fun ν hν hj => ?_) (fun ν hν => ?_) κ _ a (T - w₁.im) (fun w hw => ?_)
  · rw [two_sum_eq_trace X hν₀ hs.1, htr, Rat.cast_intCast]
  · obtain ⟨ν₁, h1, rfl, h3, h4⟩ := hfr ν hν
    rw [two_sum_eq_trace X h1 hs.1] at hj
    rw [huq ν₁ h1 h3 h4 (by exact_mod_cast hj)]
  · obtain ⟨ν₁, h1, rfl, -, h4⟩ := hfr ν hν
    obtain ⟨m, hm⟩ := h4 sE hsL
    exact ⟨m, by rw [two_sum_eq_trace X h1 hs.1, hm, Rat.cast_intCast]⟩
  · have := ha (w₁ + w) (by rw [Complex.add_im]; linarith)
    simp only [add_sub_cancel_left, eTwoPi, mul_add, Complex.exp_add] at this
    exact this

theorem frChg_of_anLie {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) (y y' : FrPt Xo c (CAt σ))
    (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)) (h : AnLie Fu i Pm y z) (h' : AnLie Fu i Pm y' z) :
    ∃ s, FrChg (fun _ => 1) s y y' := by
  have hx : y'.x = y.x := h'.1.trans h.1.symm
  obtain ⟨G, s, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  obtain ⟨-, hder, -⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Fu i _ hP
  refine ⟨s, hx, fun τ k => ?_, hG.2.2⟩
  rw [(hder _).unique (h'.2 τ k) (h.2 τ k)]
  exact (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) y y y).1.2.1 τ k

theorem evR_eq_and_norm (hL : Out.Laws) (hL2 : Out.Laws2) (U : Unf Xo c σ r) (Uw : UnfWit U)
    (hEv : GlobalTheory.Reg.EvLaws Xo c) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom)
    (y : FrPt Xo c (CAt σ)) (s : CAt σ) (v : ℝ) (hchg : FrChg (fun _ => 1) s (U.un k x) y)
    (i : Fin Uw.F.n) (Pm : (Uw.F.Di i).La →+ (Fin Uw.g → ℂ)) (hPm : IsPeriod (Uw.F.Di i) (fun j => relab c σ (Uw.e j).1) Pm)
    (hy : y.x = Uw.F.u i Pm) (hv : IsThetaL2NormSquared Uw.F i Pm y v) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c)
    (hD : Dom a n) (hF : F ∈ sec Xo c a n) :
    toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 ∧
      ‖toC (evR Xo c F y)‖ = v ^ ((n : ℝ) / 2) * ‖rdU U F k x.1‖ * (U.X k).nfac (laU U 0 n k) x.1 := by
  obtain ⟨hr, hty, -, -, hsec, -⟩ := hU
  haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  obtain ⟨b, hb, h, hun⟩ := GlobalTheory.ValNorm.exists_unit (U.X k) x.2
  obtain ⟨t, G, hbor, hG, hw⟩ := GlobalTheory.ValNorm.exists_frBor hσ U Uw k hr (hty k).1 (hty k).2 x b hb h
  obtain ⟨G', a₀, -, hG'⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y (U.un k ⟨_, h⟩)).1
    (hG.1.trans hchg.1.symm)
  have hts : (t none : CAt σ) = a₀ * s :=
    ((GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).2 _ _ _ _ hG
      ((GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c (CAt σ) _ _ _).2 _ _ _ _ hchg hG')).2
  obtain ⟨hv0, hv1⟩ := GlobalTheory.T.theta_l2_family_uniform_compare hL hL2 E H Dw l Xo c σ _ _ Uw.F _ _ _ _ y _ G' _ v 1 hPm
    (Uw.period k ⟨_, h⟩) hy (Uw.lie k ⟨_, h⟩).1 hG' hv (Uw.norm k ⟨_, h⟩ hun)
  obtain ⟨hB, hS⟩ := (GlobalTheory.T.framedPoint_eval_natural_weight_scaling E H Dw l Xo c hEv a n F hF (CAt σ)).2 inferInstance
  have hrd : ∀ z : (U.X k).dom, rdU U F k z.1 = toC (evR Xo c F (U.un k z)) := fun z => dif_pos z.2
  have e1 : toC (evR Xo c F y) = toC s ^ n * rdU U F k x.1 := by
    rw [hrd]; exact hS s _ _ hchg
  have e2 : toC (wchar (ex Dw a n) t) * rdU U F k x.1 = bchar (laU U a n k) b * rdU U F k x.1 := by
    rw [← (hsec a n hD F hF k).2.1 x.1 x.2 b hb, hrd x]
    exact ((hrd ⟨_, h⟩).trans (hB t _ _ hbor)).symm
  have e3 : (U.X k).nfac (laU U 0 n k) x.1 = ‖bchar (laU U 0 n k) b‖ := by
    rw [← GlobalTheory.NormFactor.norm_bchar_mul_nfac_rmul (U.X k) _ x.2 hb]
    unfold Data.nfac
    simp only [norm_div, hun, div_one, Real.one_rpow, Finset.prod_const_one, mul_one]
  refine ⟨e1, ?_⟩
  rw [e1, e3]
  by_cases hP : rdU U F k x.1 = 0
  · simp [hP]
  have e4 := hw a n
  rw [mul_right_cancel₀ hP e2, mul_comm] at e4
  have e5 := mul_right_cancel₀ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.bchar_ne (U.X k) _ hb) e4
  have e6 : toC (t none : CAt σ) = toC (a₀ : CAt σ) * toC s := hts
  have e7 : v ^ ((n : ℝ) / 2) * ‖toC (a₀ : CAt σ)‖ ^ n = 1 := by
    obtain ⟨m, rfl⟩ := hD.2
    rw [show (((m + m : ℕ) : ℝ) / 2) = (m : ℝ) by push_cast; ring, Real.rpow_natCast, ← two_mul, pow_mul,
      ← mul_pow, mul_comm, ← hv1, one_pow]
  rw [e5, e6, norm_mul, norm_pow, norm_pow, norm_mul, mul_pow]
  linear_combination (-(‖toC s‖ ^ n * ‖rdU U F k x.1‖)) * e7

theorem tau_col_const [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] {O : Type} [CommRing O]
    {β : O →+* c.F} {Y : Model Xo c β} {a : ArcIn Dw l β ℂ (σ.comp β)} {χ : Sp (PowerSeries ℂ) ⟶ Y.X} {W : Wit Y a χ}
    {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty}
    (Ha : HolArc Y σ a χ W Fu) {th : a.D₀.P.L.Sec} (Θ : ThetaDat Ha th) (w w' : ℂ) (j k : Fin g) (hk : k ∉ Θ.S) :
    Θ.τ w j k = Θ.τ w' j k := by
  obtain ⟨nn, h1, -, -, h4, -⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hy : Ha.y (Θ.bas (Pi.single (.inr k) 1)) = 0 := (Θ.ker _).2 fun k' hk' =>
    Pi.single_eq_of_ne (fun h => hk (by rwa [← Sum.inr_injective h])) _
  have hN : Ha.N (Θ.bas (Pi.single (.inr k) 1)) = 0 := by rw [h1, h4 _ hy, map_zero]
  have e := (Θ.per w k).2
  rw [Ha.Pw_eq, hN, smul_zero, ← smul_zero w', ← hN, ← Ha.Pw_eq, (Θ.per w' k).2] at e
  simpa using (congrFun e j).symm

theorem coeff_evR_eq_fj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) [Algebra c.F ℂ⸨X⸩] (th : a.D₀.P.L.Sec) (ξ : Module.Dual ℤ a.D₀.X) (ν₀ : E) (jj : ℤ) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.Reg.EvLaws Xo c → GoodEmb c σ → IsUnf U → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → Module.finrank (𝓞 E) a.D₀.X = 1 → ξ ≠ 0 → BetaAt ξ l.M' a.be ν₀ jj → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ w₁ : ℂ, Ha.T < w₁.im → ∃ (k : U.Comp) (ξ' : Fin r → E) (sE : E) (C : ℝ), (U.X k).IsIso ξ' ∧ IsBePar ξ a.be sE ∧ (∀ τ : (U.X k).Ψ, 0 < (τ.1 sE).re) ∧ (∀ (N : ℕ) (s : E), LevelPar ξ N s → ∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (N : E) • u) ∧ 0 < C ∧ (∀ v, Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → C ≤ v * Real.sqrt |((NumberField.discr E : ℤ) : ℝ)|) ∧ ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)) (y : FrPt Xo c ℂ⸨X⸩), IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ i, AnVec Ha (e τ i) (z τ i)) → ∃ (x : (U.X k).dom) (κ : ℂ), ∃ (L : (Fin Uw.g → ℂ) ≃ₗ[ℂ] (Fin Uw.g → ℂ)) (γ : (Uw.F.Di Ha.i).La ≃ₗ[𝓞 E] (Uw.F.Di (Uw.ik k)).La), (∀ v, Uw.Pm k x (γ v) = L (Ha.Pw w₁ v)) ∧ (∀ v v', (Uw.F.Di (Uw.ik k)).EF (γ v) (γ v') = (Uw.F.Di Ha.i).EF v v') ∧ (∀ τ i, L (z τ i) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ∧ (∃ t, (∀ v', -(Uw.F.Di Ha.i).EF t v' = ξ (Ha.y v')) ∧ (Uw.φ k (γ t) : Fin r → E) = ξ') ∧ ‖κ‖ = (C * ∏ τ, ((U.X k).tt ξ' x.1 τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x.1 ∧ ∀ F ∈ sec Xo c a' n, (U.X k).IsBddSec (laU U a' n k) (rdU U F k) → (evR Xo c F y).coeff jj * eTwoPi w₁ ^ jj = κ * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ r U Uw _ _ O _ β Y a χ W Ha _ th ξ ν₀ jj a' n hEv hσ hU halg hχ hmono hpush hth
    hrk hξ0 hβ hD hTr w₁ hw₁
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha
    ((GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 Dw Uw.g Uw.e) th hth
  obtain ⟨k, ξ', sE, hiso, hbe, hpos, hlev, hdict⟩ :=
    GlobalTheory.ArcFlow.holArc_eq_flow_orbit hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha hσ hU hrk ξ hξ0 w₁ hw₁
  obtain ⟨C₀, hC₀, hC₀', hcov⟩ := GlobalTheory.LatticeCovolumeL2.det_im_eq_covol E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ k ξ' hσ hU hiso hrk
  set B : ℝ := ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (Uw.g - Θ.S.card) * ((((Θ.τ w₁).map Complex.im).submatrix
    (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ with hBdef
  have hB : 0 < B := by
    have h1 := ((Θ.pos w₁ hw₁).2.submatrix (e := fun k : {k // k ∉ Θ.S} => k.1) Subtype.val_injective).det_pos
    have h2 := norm_pos_iff.2 Θ.κ_ne
    positivity
  refine ⟨k, ξ', sE, B * C₀, hiso, hbe, hpos, hlev, mul_pos hB hC₀, fun v hv => ?_, fun e z y hy hz => ?_⟩
  · rw [GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w₁ v hw₁ hv]
    exact mul_le_mul_of_nonneg_left hC₀' hB.le
  have hzt := GlobalTheory.T.arc_letter_analyticVectors_independent_blockType hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha y e th z hσ halg (GlobalTheory.ThetaShiftProofs.mono_j Y hmono) hy hz
  obtain ⟨x, hx, L, γ, hEF, hLz, ⟨t, ht, htξ⟩, hflow⟩ := hdict z hzt
  obtain ⟨T', hT'⟩ := GlobalTheory.T.hasSum_sectionValue_arc_framedPoint hL hL2 E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha y e th Θ z hEv halg hχ hmono hpush hth hy hz
  set K : ℝ := (B * C₀ * ∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) * (U.X k).nfac (laU U 0 n k) x with hKdef
  have htt : ∀ x' ∈ (U.X k).dom, 0 < ∏ τ, ((U.X k).tt ξ' x' τ)⁻¹ := fun x' hx' =>
    Finset.prod_pos fun τ _ => inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso hx' τ)
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos (mul_pos (mul_pos hB hC₀) (htt x hx)) _)
    (MinimumGrowthBounds.nfac_pos _ _ hx)
  let fl : ℂ → Frame (U.X k).Ψ r := fun w => (U.X k).flow ξ' (fun τ => (w - w₁) * ((τ.1 sE).re : ℂ)) x
  have key : ∀ w : ℂ, ∃ cw : ℂ, max Ha.T T' < w.im → ∀ F ∈ sec Xo c a' n,
      HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (cw * rdU U F k (fl w)) ∧
        ‖cw * rdU U F k (fl w)‖ = K * ‖rdU U F k (fl w)‖ := by
    intro w
    by_cases hw : max Ha.T T' < w.im
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    obtain ⟨hw1, hw2⟩ := max_lt_iff.1 hw
    obtain ⟨hxw, hPm, hlie⟩ := hflow w hw1
    obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr hL hL2 E H Dw l Xo c σ r U Uw O β Y a χ W Ha th Θ z hσ hzt w hw1
    obtain ⟨s, hs⟩ := frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw1) _ _ z hlie hyw.1
    have hv := GlobalTheory.ThetaSquareIntegrable.theta_l2_of_analytic_generator E H Dw l Xo c σ O β Y a χ W _ _ Uw.F Ha th Θ w yw hw1 hyw.1.1 hyw.2
    have hoff : (((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) =
        (((Θ.τ w₁).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)) := by
      ext i j
      exact congrArg Complex.im (tau_col_const Ha Θ w w₁ i.1 j.1 j.2)
    rw [hcov w ⟨_, hxw⟩ L γ hw1 hPm hEF ⟨t, fun v' hv' => by
      have := ht v'
      rwa [hv', map_zero, neg_eq_zero] at this, htξ⟩, hoff, ← mul_assoc, ← mul_assoc, ← hBdef] at hv
    refine ⟨toC s ^ n, fun _ F hF => ?_⟩
    obtain ⟨e1, e2⟩ := evR_eq_and_norm hL hL2 U Uw hEv hσ hU k ⟨_, hxw⟩ yw s _ hs Ha.i _ (Ha.period w hw1) hyw.1.1 hv
      a' n F hD hF
    have hsum := hT' w hw2 yw hyw a' n F hF
    rw [e1] at hsum e2
    refine ⟨hsum, e2.trans ?_⟩
    have hn := GlobalTheory.ArcQ.nfac_parallel_flow E H Dw l Xo c σ r U k n ξ' hD.2 hiso x hx _ hxw
    rw [hKdef, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hxw).le, Real.mul_rpow (mul_pos hB hC₀).le (htt _ hx).le]
    dsimp only [fl]
    linear_combination ((B * C₀) ^ ((n : ℝ) / 2) * ‖rdU U F k (fl w)‖) * hn
  choose cw hcw using key
  have hfl : Differentiable ℂ fl := (FlowMeanContinuity.flow_differentiable (U.X k) ξ' x).comp (by fun_prop)
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.exists_const_ratio_of_norm_eq {F // F ∈ sec Xo c a' n} (max Ha.T T') K
    (fun F w => cw w * rdU U F.1 k (fl w)) (fun F w => rdU U F.1 k (fl w)) cw hK
    (fun F => ⟨differentiableOn_of_hasSum _ _ _ fun w hw => (hcw w hw F.1 F.2).1,
      (hU.2.2.2.2.1 a' n hD F.1 F.2 k).1.comp hfl.differentiableOn
        fun w hw => (hflow w (max_lt_iff.1 hw).1).1⟩)
    (fun F w hw => ⟨rfl, (hcw w hw F.1 F.2).2⟩)
  refine ⟨⟨x, hx⟩, κ, L, γ, fun v => ?_, hEF, hLz, ⟨t, ht, htξ⟩, hκ, fun F hF hbdd => ?_⟩
  · obtain ⟨h1, h2, -⟩ := hflow w₁ hw₁
    rw [← h2 v]
    congr 3
    simp only [sub_self, zero_mul]
    exact (EmbeddingHermitianPairs.flow_zero _ _ _).symm
  · refine coeff_eq_of_betaAt (U.X k) hbdd hiso hx ξ l.M' a.be
      (fun y z => (dvd_mul_left _ 2).trans (a.be_dvd y z)) hβ hbe hpos (hTr k) (hlev _) κ w₁ _ (max Ha.T T')
      fun w hw => ?_
    exact hκ' ⟨F, hF⟩ w hw ▸ (hcw w hw F hF).1

end GlobalTheory.ArcCoeff
