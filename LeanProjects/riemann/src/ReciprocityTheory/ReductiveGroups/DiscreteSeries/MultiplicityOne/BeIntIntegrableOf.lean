import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SigIntIntegrable

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def MinorsOn (D : RealPlaceData k r Wp Wp) (X : SigData k r) : Prop :=
  ∀ u₁ ∈ Vfl X, ∀ u₂ ∈ Vfl X, ∀ u₃ ∈ Vfl X, ∀ u₄ ∈ Vfl X, ∀ e₁ e₂ e₃ e₄ : Wp,
    ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ =
      ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

lemma beInt_add_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u v u' : X.Hs) (p : Mt k r × Mt k r) :
    beInt D X (u + v) u' p = beInt D X u u' p + beInt D X v u' p := by
  simp only [beInt, mc, map_add, inner_add_right, add_mul, add_smul]

lemma beInt_smul_left (D : RealPlaceData k r Wp Wp) (X : SigData k r) (c : ℂ) (u u' : X.Hs)
    (p : Mt k r × Mt k r) : beInt D X (c • u) u' p = c • beInt D X u u' p := by
  simp only [beInt, mc, map_smul, inner_smul_right, smul_smul, mul_assoc]

theorem beInt_integrable_of (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) :
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN) := by
  intro u hu u' hu'
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd X.a X.a u hu u' hu'
  refine h1' k r Wp D X hD hX (X.a - AG k r - 1) ?_ u u' ⟨C, ?_⟩
  · have hn : (1 : ℝ) ≤ nR k r := by
      unfold nR
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    unfold AS AG
    unfold aM at ha
    nlinarith [mul_nonneg (sub_nonneg.2 hn) (by positivity : (0 : ℝ) ≤ 3 * nR k r ^ 2 + 2 * nR k r + 2)]
  · simpa [min_self] using hC

theorem multOne_of_minors (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hH : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ)
    (hP : ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re)
    (hInt : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, Integrable (beInt D X u u') (D.μW.prod D.μN))
    (hEq : ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r,
        beOp D X (X.σ (m * h) u) u' = psiD D m • (D.π h).comp (beOp D X u u'))
    (hM : MinorsOn D X) : ∃ l : X.Hs → Wp, IsMultOneMap D X l := by
  have hre : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = ((⟪ξ, beOp D X u u ξ⟫_ℂ).re : ℂ) := by
    intro u hu ξ
    have h1 := hH u hu u hu ξ ξ
    have h2 : starRingEnd ℂ ⟪ξ, beOp D X u u ξ⟫_ℂ = ⟪ξ, beOp D X u u ξ⟫_ℂ := by
      rw [inner_conj_symm]; exact h1.symm
    exact (Complex.conj_eq_iff_re.mp h2).symm
  by_cases h0 : ∃ v₀ ∈ Vfl X, ∃ ξ₀ : Wp, 0 < (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re
  · obtain ⟨v₀, hv₀, ξ₀, hpos⟩ := h0
    set κ₀ : ℝ := (⟪ξ₀, beOp D X v₀ v₀ ξ₀⟫_ℂ).re with hκ₀
    set c : ℂ := (((Real.sqrt κ₀)⁻¹ : ℝ) : ℂ) with hc
    refine ⟨fun u => c • beOp D X u v₀ ξ₀, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro u hu v hv
      have : beOp D X (u + v) v₀ = beOp D X u v₀ + beOp D X v v₀ := by
        unfold beOp
        simp_rw [beInt_add_left]
        exact integral_add (hInt u hu v₀ hv₀) (hInt v hv v₀ hv₀)
      simp only [this, _root_.add_apply, smul_add]
    · intro a u hu
      have : beOp D X (a • u) v₀ = a • beOp D X u v₀ := by
        unfold beOp
        simp_rw [beInt_smul_left]
        exact integral_smul a _
      simp only [this, _root_.smul_apply]
      rw [smul_comm]
    · intro h hh m hm u hu
      simp only [hEq u hu v₀ hv₀ h hh m hm, _root_.smul_apply,
        ContinuousLinearMap.comp_apply, map_smul]
      rw [smul_comm]
    · intro u hu u' hu'
      ext η'
      apply ext_inner_left ℂ
      intro η
      simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
        inner_smul_left]
      rw [← hH v₀ hv₀ u' hu' η' ξ₀]
      have hmin := hM u hu u' hu' v₀ hv₀ v₀ hv₀ η η' ξ₀ ξ₀
      rw [hre v₀ hv₀ ξ₀] at hmin
      have hcc : starRingEnd ℂ c * c = ((κ₀⁻¹ : ℝ) : ℂ) := by
        rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul]
        congr 1
        rw [← mul_inv, Real.mul_self_sqrt hpos.le]
      have hk : ((κ₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      calc ⟪η, beOp D X u u' η'⟫_ℂ
          = (starRingEnd ℂ c * c) * (⟪η, beOp D X u u' η'⟫_ℂ * (κ₀ : ℂ)) := by
            rw [hcc, Complex.ofReal_inv]; field_simp
        _ = _ := by rw [hmin]; ring
  · push Not at h0
    have hz : ∀ u ∈ Vfl X, ∀ ξ : Wp, ⟪ξ, beOp D X u u ξ⟫_ℂ = 0 := by
      intro u hu ξ
      rw [hre u hu ξ]
      have := le_antisymm (h0 u hu ξ) (hP u hu ξ)
      simp [this]
    refine ⟨fun _ => 0, ⟨fun _ _ _ _ => by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩, ?_⟩
    intro u hu u' hu'
    ext η'
    apply ext_inner_left ℂ
    intro η
    have hm := hM u hu u' hu' u' hu' u hu η η' η' η
    rw [hz u hu η, zero_mul] at hm
    have hc : ⟪η', beOp D X u' u η⟫_ℂ = starRingEnd ℂ ⟪η, beOp D X u u' η'⟫_ℂ := by
      rw [hH u' hu' u hu η η', inner_conj_symm]
    rw [hc, Complex.mul_conj] at hm
    have h3 : Complex.normSq ⟪η, beOp D X u u' η'⟫_ℂ = 0 := by exact_mod_cast hm
    rw [Complex.normSq_eq_zero.mp h3]
    simp [rk1]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def Mn (D : RealPlaceData k r Wp Wp) (X : SigData k r) (u₁ u₂ u₃ u₄ : X.Hs) (e₁ e₂ e₃ e₄ : Wp) : ℂ :=
  ⟪e₁, beOp D X u₁ u₂ e₂⟫_ℂ * ⟪e₃, beOp D X u₃ u₄ e₄⟫_ℂ -
    ⟪e₁, beOp D X u₁ u₄ e₄⟫_ℂ * ⟪e₃, beOp D X u₃ u₂ e₂⟫_ℂ

theorem kbound (B : Wp →L[ℂ] Wp) (e f : Wp) : ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖f‖ * ‖B‖ := by
  calc ‖⟪e, B f⟫_ℂ‖ ≤ ‖e‖ * ‖B f‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖B‖ * ‖f‖) := mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg _)
    _ = _ := by ring

theorem joint_int (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {b Cl : ℝ} (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    Integrable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2) *
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ * Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := by
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  obtain ⟨K, hK, M, hM0, R, hR0, hRK, hM⟩ := test_bound hφ
  have a1 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => φ (Matrix.of z.2)) (D.μG.prod D.μG) :=
    (aesm_G D (test_cont hφ)).comp_snd
  have a2 : AEStronglyMeasurable (fun z : Mt k r × Mt k r =>
      ⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ) (D.μG.prod D.μG) :=
    ((sig_aesm D X X.w).comp_fst).inner ((sig_aesm D X X.w).comp_snd)
  have a3 : AEStronglyMeasurable (fun z : Mt k r × Mt k r => Λ (X.σ (Matrix.of z.1) X.w))
      (D.μG.prod D.μG) := hlm.comp_fst
  have hint : Integrable (fun z : Mt k r × Mt k r =>
      (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl * gN (Matrix.of z.1) ^ (-(X.a - b))) *
        K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2)) (D.μG.prod D.μG) :=
    ((gN_integrable D hGN hab).const_mul (M * X.Cw * (KH k r ^ 2 * R) ^ X.a * Cl)).mul_prod (int_ind D hK)
  refine hint.mono' ((a1.mul a2).mul a3) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_G D),
    Measure.quasiMeasurePreserving_snd.ae (ae_G D)] with z hz1 hz2
  have hKp : 0 ≤ (KH k r ^ 2 * R) ^ X.a := Real.rpow_nonneg (mul_nonneg (pow_pos KH_pos 2).le hR0) _
  have hCw := C_nonneg X.dec
  by_cases hxK : Matrix.of z.2 ∈ K
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 1 := by simp [Set.indicator, hxK]
    have hφx : ‖φ (Matrix.of z.2)‖ ≤ M := by simpa [hi] using hM _ hz2
    have hO' : ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ ≤
        X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a)) :=
      (orbit_bound X ha0 hz2 hz1).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (mul_nonneg (pow_pos KH_pos 2).le (gN_nonneg _))
          (mul_le_mul_of_nonneg_left (hRK _ hxK) (pow_pos KH_pos 2).le) ha0)
        (Real.rpow_nonneg (gN_nonneg _) _)) hCw)
    have hl := hCl _ hz1
    have e : gN (Matrix.of z.1) ^ (-(X.a - b)) =
        gN (Matrix.of z.1) ^ (-X.a) * gN (Matrix.of z.1) ^ b := by
      rw [← Real.rpow_add (gN_pos hz1)]; ring_nf
    rw [norm_mul, norm_mul, hi, mul_one, e]
    calc ‖φ (Matrix.of z.2)‖ * ‖⟪X.σ (Matrix.of z.1) X.w, X.σ (Matrix.of z.2) X.w⟫_ℂ‖ *
          ‖Λ (X.σ (Matrix.of z.1) X.w)‖
        ≤ M * (X.Cw * ((KH k r ^ 2 * R) ^ X.a * gN (Matrix.of z.1) ^ (-X.a))) *
          (Cl * gN (Matrix.of z.1) ^ b) :=
          mul_le_mul (mul_le_mul hφx hO' (norm_nonneg _) hM0) hl (norm_nonneg _)
            (mul_nonneg hM0 (mul_nonneg hCw (mul_nonneg hKp (Real.rpow_nonneg (gN_nonneg _) _))))
      _ = _ := by ring
  · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of z.2) = 0 := by simp [Set.indicator, hxK]
    have hφx : φ (Matrix.of z.2) = 0 := by
      have := hM _ hz2; rw [hi, mul_zero] at this; exact norm_le_zero_iff.1 this
    rw [hφx, hi]
    simp

theorem step_ii (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b Cl : ℝ} (hd : 0 < d) (hCl0 : 0 ≤ Cl) (hab : AB k r ≤ X.a - b) (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hCl : ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ Cl * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    ∫ x : Mt k r, φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) ∂D.μG = Λ (sigInt D X φ X.w) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hint := sigInt_integrable D X hφ
  have hc : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, sigInt D X φ X.w⟫_ℂ =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG := by
    intro y
    unfold sigInt
    rw [← integral_inner hint]
    simp only [inner_smul_right]
  have hFi := joint_int D X hGN ha0 hCl0 hab Λ hlm hCl hφ
  have e1 : Λ (sigInt D X φ X.w) = (d : ℂ) * ∫ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) ∂D.μG := by
    rw [hR _ (dd_mem D X ha0 hφ)]
    simp only [hc]
  have e2 : ∀ y : Mt k r, (∫ x : Mt k r, φ (Matrix.of x) *
        ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ ∂D.μG) * Λ (X.σ (Matrix.of y) X.w) =
      ∫ x : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG := fun y => (integral_mul_const _ _).symm
  have e3 := integral_integral_swap (μ := D.μG) (ν := D.μG) (f := fun y x : Mt k r => φ (Matrix.of x) *
      ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ * Λ (X.σ (Matrix.of y) X.w)) hFi
  have e4 : ∀ᵐ x ∂D.μG, ∫ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) ∂D.μG = φ (Matrix.of x) * Λ (X.σ (Matrix.of x) X.w) / d := by
    filter_upwards [ae_G D] with x hx
    have hx' := hR _ (sig_mem_vfl X ha0 hx (w_mem X))
    have e5 : ∀ y : Mt k r, φ (Matrix.of x) * ⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w) = φ (Matrix.of x) * (⟪X.σ (Matrix.of y) X.w, X.σ (Matrix.of x) X.w⟫_ℂ *
        Λ (X.σ (Matrix.of y) X.w)) := fun y => mul_assoc _ _ _
    simp only [e5]
    rw [integral_const_mul, hx']
    field_simp
  rw [e1]
  simp only [e2]
  rw [e3, integral_congr_ae e4, integral_div]
  field_simp

theorem vanish_core (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hGN : GNIntSharp)
    (ha0 : 0 ≤ X.a) {d b : ℝ} (hd : 0 < d) (hb0 : 0 ≤ b) (hab : AB k r ≤ X.a - b)
    (Λ : X.Hs → ℂ)
    (hlm : AEStronglyMeasurable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG)
    (hlb : ∃ C : ℝ, ∀ y ∈ GV k r, ‖Λ (X.σ y X.w)‖ ≤ C * gN y ^ b)
    (hR : ∀ u ∈ Vfl X, Λ u = (d : ℂ) *
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG)
    (h0 : ∀ φ : Mat k r → ℂ, IsTestG φ → Λ (sigInt D X φ X.w) = 0) :
    ∀ u ∈ Vfl X, Λ u = 0 := by
  obtain ⟨Cl, hCl⟩ := hlb
  have hCl0 : 0 ≤ Cl := C_nonneg hCl
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  have hli : LocallyIntegrable (fun y : Mt k r => Λ (X.σ (Matrix.of y) X.w)) D.μG := by
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn gN_cont.continuousOn
    have hfin : IsFiniteMeasure (D.μG.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact D.haarG.finite_compact K hK⟩
    refine Integrable.mono' (integrable_const (Cl * (max R 0) ^ b)) hlm.restrict ?_
    filter_upwards [ae_restrict_mem hK.measurableSet, ae_restrict_of_ae (ae_G D)] with y hyK hyG
    refine (hCl _ hyG).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (gN_nonneg _) ?_ hb0) hCl0)
    exact ((Real.le_norm_self _).trans (hR y hyK)).trans (le_max_left _ _)
  have hae : ∀ᵐ y ∂D.μG, Λ (X.σ (Matrix.of y) X.w) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli fun g hg hgc => ?_
    have h1 := step_ii D X hGN ha0 hd hCl0 hab Λ hlm hCl hR (test_of_contDiff hg hgc)
    rw [h0 _ (test_of_contDiff hg hgc)] at h1
    rw [← h1]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => Complex.real_smul)
  intro u hu
  rw [hR u hu]
  have : ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ * Λ (X.σ (Matrix.of y) X.w) ∂D.μG = 0 :=
    integral_eq_zero_of_ae (by filter_upwards [hae] with y hy; simp [hy])
  rw [this, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
