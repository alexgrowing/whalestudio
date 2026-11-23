import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.FlagUnipotentLattices.KappaAssemblyOf
import Formalism.FlagUnipotentLattices.CuspThresholdBound

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

abbrev cu_mu (X : CData) : Measure X.I.GA := X.I.muA X.μf

instance cu_sfin (X : CData) : SigmaFinite (cu_mu X) := by
  unfold cu_mu AutInst.muA
  infer_instance

theorem cu_leftInv (X : CData) (hf : X.μf.IsHaarMeasure) : (cu_mu X).IsMulLeftInvariant := by
  unfold cu_mu AutInst.muA
  have h1 : (Measure.pi fun v => Formalism.REAL.muG (X.I.ε v)).IsMulLeftInvariant := inferInstance
  have h2 : X.μf.IsMulLeftInvariant := inferInstance
  have h3 : MeasurableMul X.I.Gf := inferInstance
  exact Measure.prod.instIsMulLeftInvariant

def cu_cst (X : CData) (ν : Measure X.I.GA) (f : X.I.GA → ℂ) (x : X.I.GA) : ℂ := ∫ m, f (m * x) ∂ν

structure cu_NObj (X : CData) where
  μN : ∀ v : InfinitePlace X.I.F, Measure (Formalism.REAL.UJ (X.I.ε v))
  [sN : ∀ v, SigmaFinite (μN v)]
  μNf : Measure X.I.Gf
  [sNf : SigmaFinite μNf]
  lam : Measure X.I.GA

attribute [instance] cu_NObj.sN cu_NObj.sNf

namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def μNA : Measure X.I.GA := (Measure.pi O.μN).prod O.μNf

def IsOn (W : Submodule X.I.E (Fin X.I.n → X.I.E)) : Prop := O.μNA (X.I.NA W)ᶜ = 0

def IsWeil : Prop :=
  ∀ F : X.I.GA → ℂ, Integrable F (cu_mu X) → ∫ y, F y ∂(cu_mu X) = ∫ y, ∫ n, F (n * y) ∂O.μNA ∂O.lam

def CstInv (ν : Measure X.I.GA) (f : X.I.GA → ℂ) : Prop :=
  ∀ᵐ y ∂O.lam, ∃ c : ℂ, ∀ᵐ n ∂O.μNA, cu_cst X ν f (n * y) = c

def PhPZero (x : X.I.GA) : Prop :=
  ∃ v, ∀ᵐ y ∂O.lam, ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)) ∂(O.μN v) = 0

theorem inner_eq (x y : X.I.GA) :
    ∫ n, X.φ (x⁻¹ * (n * y)) ∂O.μNA =
      (∏ v, ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)) ∂(O.μN v)) *
        ∫ n, X.e (x.2⁻¹ * (n * y.2)) ∂O.μNf := by
  unfold μNA
  rw [← integral_fintype_prod_eq_prod (𝕜 := ℂ) (μ := O.μN)
    (fun v n => phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * y.1 v)))]
  rw [← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  show X.φ (x⁻¹ * (n * y)) = _
  unfold CData.φ phe
  rw [X.phOf_eq_prod]
  rfl

theorem inner_zero {x : X.I.GA} (h : O.PhPZero x) : ∀ᵐ y ∂O.lam, ∫ n, X.φ (x⁻¹ * (n * y)) ∂O.μNA = 0 := by
  obtain ⟨v, hv⟩ := h
  filter_upwards [hv] with y hy
  rw [O.inner_eq, Finset.prod_eq_zero (Finset.mem_univ v) hy, zero_mul]

end cu_NObj

def cu_Repro (X : CData) (ν : Measure X.I.GA) (f : X.I.GA → ℂ) : Prop :=
  ∀ᵐ x ∂(cu_mu X),
    Integrable (fun p : X.I.GA × X.I.GA => f (p.1 * x * p.2) * X.φ p.2) (ν.prod (cu_mu X)) ∧
      ∀ᵐ m ∂ν, f (m * x) = ∫ g, f (m * x * g) * X.φ g ∂(cu_mu X)

theorem cu_cst_repro (X : CData) (ν : Measure X.I.GA) [IsFiniteMeasure ν] (f : X.I.GA → ℂ) (x : X.I.GA)
    (hint : Integrable (fun p : X.I.GA × X.I.GA => f (p.1 * x * p.2) * X.φ p.2) (ν.prod (cu_mu X)))
    (hrep : ∀ᵐ m ∂ν, f (m * x) = ∫ g, f (m * x * g) * X.φ g ∂(cu_mu X)) :
    Integrable (fun g => cu_cst X ν f (x * g) * X.φ g) (cu_mu X) ∧
      cu_cst X ν f x = ∫ g, cu_cst X ν f (x * g) * X.φ g ∂(cu_mu X) := by
  have e1 : ∀ g, cu_cst X ν f (x * g) * X.φ g = ∫ m, f (m * x * g) * X.φ g ∂ν := by
    intro g
    unfold cu_cst
    rw [integral_mul_const]
    simp only [mul_assoc]
  constructor
  · have := hint.integral_prod_right
    exact this.congr (Filter.Eventually.of_forall fun g => (e1 g).symm)
  · calc cu_cst X ν f x = ∫ m, ∫ g, f (m * x * g) * X.φ g ∂(cu_mu X) ∂ν := integral_congr_ae hrep
      _ = ∫ g, ∫ m, f (m * x * g) * X.φ g ∂ν ∂(cu_mu X) :=
          integral_integral_swap (f := fun m g => f (m * x * g) * X.φ g) hint
      _ = ∫ g, cu_cst X ν f (x * g) * X.φ g ∂(cu_mu X) :=
          integral_congr_ae (Filter.Eventually.of_forall fun g => (e1 g).symm)

theorem cu_cst_zero (X : CData) (hL : (cu_mu X).IsMulLeftInvariant) (ν : Measure X.I.GA) [IsFiniteMeasure ν]
    (f : X.I.GA → ℂ) (x : X.I.GA)
    (hint : Integrable (fun p : X.I.GA × X.I.GA => f (p.1 * x * p.2) * X.φ p.2) (ν.prod (cu_mu X)))
    (hrep : ∀ᵐ m ∂ν, f (m * x) = ∫ g, f (m * x * g) * X.φ g ∂(cu_mu X))
    (O : cu_NObj X) (hW : O.IsWeil) (hI : O.CstInv ν f) (hZ : O.PhPZero x) : cu_cst X ν f x = 0 := by
  obtain ⟨h1, h2⟩ := cu_cst_repro X ν f x hint hrep
  set F : X.I.GA → ℂ := fun y => cu_cst X ν f y * X.φ (x⁻¹ * y) with hF
  have e2 : ∀ g, F (x * g) = cu_cst X ν f (x * g) * X.φ g := fun g => by
    simp only [hF, inv_mul_cancel_left]
  have hFint : Integrable F (cu_mu X) := by
    have := h1.comp_mul_left x⁻¹
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hF, mul_inv_cancel_left]
  rw [h2, ← integral_congr_ae (Filter.Eventually.of_forall e2), integral_mul_left_eq_self F x, hW F hFint]
  have hz : ∀ᵐ y ∂O.lam, ∫ n, F (n * y) ∂O.μNA = 0 := by
    filter_upwards [hI, O.inner_zero hZ] with y hy hy0
    obtain ⟨c, hc⟩ := hy
    have : ∫ n, F (n * y) ∂O.μNA = ∫ n, c * X.φ (x⁻¹ * (n * y)) ∂O.μNA :=
      integral_congr_ae (hc.mono fun n hn => by simp only [hF, hn])
    rw [this, integral_const_mul, hy0, mul_zero]
  rw [integral_congr_ae hz, integral_zero]

namespace cu

variable (X : CData)

def ReproStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      cu_Repro X ν (X.I.ext Fv)

def UnipStep : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∃ O : cu_NObj X, O.IsOn W ∧ O.IsWeil ∧
    (∀ x, O.PhPZero x) ∧
    ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
      ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν → O.CstInv ν (X.I.ext Fv)

end cu

theorem cuspidal_range_of_repro_unipotent (X : CData) (hf : X.μf.IsHaarMeasure) (hR : cu.ReproStep X) (hU : cu.UnipStep X) :
    X.CuspStep := by
  intro T hT hP Fv hFv W hW ν hν
  have := hν.1
  obtain ⟨O, -, hWeil, hZ, hI⟩ := hU W hW
  filter_upwards [hR T hT hP Fv hFv W hW ν hν] with x hx
  exact cu_cst_zero X (cu_leftInv X hf) ν (X.I.ext Fv) x hx.1 hx.2 O hWeil (hI T hT hP Fv hFv ν hν) (hZ x)

def cu_wt (X : CData) (s : ℝ) (g : X.I.GA) : ℝ := Real.exp (s * ∑ v, cartanDistance (X.I.ε v) (g.1 v))

namespace cu

variable (X : CData)

def HaarGrowth : Prop :=
  ∀ s : ℝ, 0 ≤ s →
    (∀ v, 1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + s < X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ))) →
    Integrable (fun g => ‖X.φ g‖ * cu_wt X s g) (cu_mu X)

def GrowthStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), ∃ B : ℝ, ∀ᵐ p ∂(ν.prod (cu_mu X)), X.φ p.2 ≠ 0 →
        ‖X.I.ext Fv (p.1 * x * p.2)‖ ≤ B * cu_wt X (2 * (X.I.n : ℝ) ^ 2) p.2

def MeasStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), AEStronglyMeasurable (fun p : X.I.GA × X.I.GA => X.I.ext Fv (p.1 * x * p.2)) (ν.prod (cu_mu X))

def PointRepro : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ ν : Measure X.I.GA, X.I.IsNQuotMeas W ν →
      ∀ᵐ x ∂(cu_mu X), ∀ᵐ m ∂ν,
        X.I.ext Fv (m * x) = ∫ g, X.I.ext Fv (m * x * g) * X.φ g ∂(cu_mu X)

end cu

theorem cu_reproStep_of (X : CData)
    (hrate : ∀ v, 1 ≤ q0At X.I v →
      2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + 2 * (X.I.n : ℝ) ^ 2 <
        X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ)))
    (hH : cu.HaarGrowth X) (hG : cu.GrowthStep X) (hM : cu.MeasStep X) (hP : cu.PointRepro X) : cu.ReproStep X := by
  intro T hT hPr Fv hFv W hW ν hν
  have := hν.1
  have hmaj := hH (2 * (X.I.n : ℝ) ^ 2) (by positivity) hrate
  filter_upwards [hG T hT hPr Fv hFv W hW ν hν, hM T hT hPr Fv hFv W hW ν hν, hP T hT hPr Fv hFv W hW ν hν]
    with x hx1 hx2 hx3
  refine ⟨?_, hx3⟩
  obtain ⟨B, hB⟩ := hx1
  have hφm : AEStronglyMeasurable (fun p : X.I.GA × X.I.GA => X.φ p.2) (ν.prod (cu_mu X)) :=
    hT.1.aestronglyMeasurable.comp_snd
  have hmaj2 : Integrable (fun p : X.I.GA × X.I.GA => B * (‖X.φ p.2‖ * cu_wt X (2 * (X.I.n : ℝ) ^ 2) p.2))
      (ν.prod (cu_mu X)) := (hmaj.comp_snd ν).const_mul B
  refine hmaj2.mono' (hx2.mul hφm) (hB.mono fun p hp => ?_)
  rw [norm_mul]
  by_cases h0 : X.φ p.2 = 0
  · simp [h0]
  · calc ‖X.I.ext Fv (p.1 * x * p.2)‖ * ‖X.φ p.2‖ ≤ (B * cu_wt X (2 * (X.I.n : ℝ) ^ 2) p.2) * ‖X.φ p.2‖ :=
          mul_le_mul_of_nonneg_right (hp h0) (norm_nonneg _)
      _ = B * (‖X.φ p.2‖ * cu_wt X (2 * (X.I.n : ℝ) ^ 2) p.2) := by ring

theorem cu_p_add_q (I : AutInst) (v : InfinitePlace I.F) : I.pAt v + I.qAt v = I.n := by
  unfold AutInst.pAt AutInst.qAt
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin I.n))) (fun a => I.ε v a = true)
  simpa using h

theorem two_q0_le_n (I : AutInst) (v : InfinitePlace I.F) : 2 * q0At I v ≤ I.n := by
  have := cu_p_add_q I v
  unfold q0At
  omega

theorem cu_thresholds (X : CData) {C : ℝ} (hC : 46 ≤ C) (h2 : X.GapAboveSquareRootThreshold C) (v : InfinitePlace X.I.F)
    (hq : 1 ≤ q0At X.I v) :
    2 * (X.I.n : ℝ) * Real.sqrt (2 * (q0At X.I v : ℝ)) + 2 * (X.I.n : ℝ) ^ 2 <
        X.h / 8 / Real.sqrt (2 * (q0At X.I v : ℝ)) ∧
      16 * (2 * (X.I.n : ℝ) ^ 2) * Real.sqrt (2 * (q0At X.I v : ℝ)) ≤ X.h ∧
      16 * (X.I.n : ℝ) * (q0At X.I v : ℝ) ^ ((3 : ℝ) / 2) < X.h := by
  have hpos : 0 ≤ (X.I.n : ℝ) ^ 2 * Real.sqrt (q0At X.I v : ℝ) := by positivity
  have h46 : 46 * (X.I.n : ℝ) ^ 2 * Real.sqrt (q0At X.I v : ℝ) ≤ X.h := by
    refine le_trans ?_ (h2 v)
    nlinarith
  have h40 : 40 * (X.I.n : ℝ) ^ 2 * Real.sqrt (q0At X.I v : ℝ) ≤ X.h := by
    refine le_trans ?_ h46
    nlinarith
  have h2q := two_q0_le_n X.I v
  refine ⟨Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.cusp_threshold_bound X.I.n (q0At X.I v) X.h hq h2q h40,
    Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.threshCount X.I.n (q0At X.I v) X.h h46,
    ((Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.threshCuspOp X.I.n (q0At X.I v) X.h hq).2 (by omega) h40).2⟩

def cu_absS (X : CData) (x : X.I.GA) : ℝ≥0∞ := ∑' γ : X.I.GFset, ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ

def cu_Kc (X : CData) (B : ℝ) : ℝ := (Real.exp B / (1 - Real.exp (-B))) ^ Fintype.card (InfinitePlace X.I.F)

theorem cu_one_le_Kc (X : CData) {B : ℝ} (hB : 0 < B) : 1 ≤ cu_Kc X B := by
  unfold cu_Kc
  apply one_le_pow₀
  have h1 : 0 < Real.exp (-B) := Real.exp_pos _
  have h2 : Real.exp (-B) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have h3 : 1 ≤ Real.exp B := Real.one_le_exp hB.le
  rw [le_div_iff₀ (by linarith)]
  linarith

open Classical in

theorem cu_absS_le (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower)
    (hE : X.LowProj) {q₀ : ℕ} (hq : ∀ v, q0At X.I v = q₀) {Ac B : ℝ} (hAc : 0 ≤ Ac) (hB : 0 < B)
    (hr : 1 ≤ q₀ → 16 * B * Real.sqrt (2 * (q₀ : ℝ)) ≤ X.h) {x : X.I.GA} (hcnt : X.FarCount Ac B {x}) :
    cu_absS X x ≤ ENNReal.ofReal (fdegAll X.I X.σ X.w * (X.e 1).re * (Ac * cu_Kc X B)) := by
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set bd : X.I.GFset → ℝ := fun γ => ∏ v, Real.exp (-(Formalism.HermitianLatticeCounting.S7.decExp X.h q₀ (X.dist x γ v))) with hbd
  have hbdn : ∀ γ, 0 ≤ bd γ := fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  unfold cu_absS
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set S : Finset X.I.GFset := s.filter (fun γ : X.I.GFset => X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0) with hS
  have hterm : ∀ γ ∈ s, ‖X.φ (x⁻¹ * (γ : X.I.GA) * x)‖ₑ ≤
      (if X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0 then ENNReal.ofReal (k0 * bd γ) else 0) := by
    intro γ _
    by_cases h0 : X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0
    · simp [h0]
    · rw [if_pos h0, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (X.norm_φ_le D hdec hX h1 hE hq _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_filter, ← ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg hk0n (hbdn γ)), ← Finset.mul_sum]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hk0n)
  have hc : ∀ r : InfinitePlace X.I.F → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, X.dist x γ v ≤ r v).card : ℝ) ≤ Ac * Real.exp (B * ∑ v, r v) := by
    intro r hr0
    refine hcnt x rfl r hr0 _ fun γ hγ => ?_
    have h3 := Finset.mem_filter.1 hγ
    exact ⟨(Finset.mem_filter.1 h3.1).2, h3.2⟩
  rcases Nat.eq_zero_or_pos q₀ with h0 | hq1
  ·
    have hd : ∀ γ v, X.dist x γ v = 0 := fun γ v => cartan_distance_eq_zero_of_definite (by have := hq v; rw [h0] at this; exact this) _
    have hb1 : ∀ γ, bd γ = 1 := fun γ => by
      simp only [hbd, hd, Formalism.HermitianLatticeCounting.S7.decExp]
      simp
    have h4 := hc (fun _ => 0) (fun _ => le_rfl)
    simp only [hd, le_refl, implies_true, Finset.filter_true, Finset.sum_const_zero, mul_zero, Real.exp_zero,
      mul_one] at h4
    simp only [hb1, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact le_trans h4 (le_mul_of_one_le_right hAc (cu_one_le_Kc X hB))
  · exact Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.allSumRate (InfinitePlace X.I.F) X.I.GFset S (X.dist x) Ac B X.h q₀ hq1 hAc hB (hr hq1)
      (fun γ _ v => cartan_distance_nonneg _ _) hc

theorem cu_range_le_kernel (X : CData) (hK : X.KernelDiag) (T : X.L2 →L[ℂ] X.L2) (hT : X.IsOp T)
    (hP : IsStarProjection T) [FiniteDimensional ℂ (X.rg T)] (Fv : X.L2) (hFv : Fv ∈ X.rg T) :
    ∀ᵐ y ∂X.μ, Summable (fun γ : X.I.GFset => X.φ (y⁻¹ * (γ : X.I.GA) * y)) ∧
      ‖(Fv : X.I.GA → ℂ) y‖ ^ 2 ≤ (∫ z, ‖(Fv : X.I.GA → ℂ) z‖ ^ 2 ∂X.μ) * (X.kerD y).re := by
  classical
  set F := stdOrthonormalBasis ℂ (X.rg T) with hF
  set Fn : Fin (Module.finrank ℂ (X.rg T)) → X.I.GA → ℂ := fun w => (((F w : X.rg T) : X.L2) : X.I.GA → ℂ) with hFn
  set c : Fin (Module.finrank ℂ (X.rg T)) → ℂ := fun w => F.repr ⟨Fv, hFv⟩ w with hc
  have horth : ∀ w w', (∫ x, star (Fn w x) * Fn w' x ∂X.μ) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 := orthonormal_iff_ite.1 F.orthonormal w w'
    rw [Submodule.coe_inner, MeasureTheory.L2.inner_def] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFn, RCLike.inner_apply]
    rw [mul_comm]
    rfl
  have hmem : ∀ w, MemLp (Fn w) 2 X.μ := fun w => Lp.memLp _
  have hsum : Fv = ∑ w, c w • ((F w : X.rg T) : X.L2) := by
    have h := F.sum_repr ⟨Fv, hFv⟩
    have h2 := congrArg (fun z : X.rg T => (z : X.L2)) h
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hae : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] fun y => ∑ w, c w * Fn w y := by
    have h1 : (Fv : X.I.GA → ℂ) =ᵐ[X.μ] ((∑ w, c w • ((F w : X.rg T) : X.L2) : X.L2) : X.I.GA → ℂ) := by
      rw [← hsum]
    refine h1.trans ((Lp.coeFn_finsetSum _ _).trans ?_)
    have h3 : ∀ w, ((c w • ((F w : X.rg T) : X.L2) : X.L2) : X.I.GA → ℂ) =ᵐ[X.μ] fun y => c w * Fn w y :=
      fun w => Lp.coeFn_smul _ _
    have h4 : ∀ᵐ y ∂X.μ, ∀ w, ((c w • ((F w : X.rg T) : X.L2) : X.L2) : X.I.GA → ℂ) y = c w * Fn w y :=
      ae_all_iff.2 h3
    filter_upwards [h4] with y hy
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun w _ => hy w
  have hint : ∫ z, ‖(Fv : X.I.GA → ℂ) z‖ ^ 2 ∂X.μ = ∫ z, ‖∑ w, c w * Fn w z‖ ^ 2 ∂X.μ :=
    integral_congr_ae (hae.mono fun z hz => by beta_reduce; rw [hz])
  filter_upwards [hae, hK T hT hP _ F] with y hy hy2
  refine ⟨hy2.1, ?_⟩
  rw [hy, hint, hy2.2, Complex.ofReal_re]
  exact Formalism.HermitianLatticeCounting.Final.S7.kernelBound X.I.GA _ X.μ Fn c hmem horth y

namespace cu

variable (X : CData)

def Act (t : ℝ) : ℝ := (3 * Real.sqrt (X.I.n : ℝ) / t ^ 2) ^ (2 * X.I.n ^ 2 * X.I.f)

def SizeStep : Prop :=
  ∃ τ : X.I.GA → ℝ, (∀ y, 0 < τ y) ∧ (∀ γ ∈ X.I.GFset, ∀ y, τ (γ * y) = τ y) ∧
    (∀ y, X.FarCount (Act X (τ y)) (2 * (X.I.n : ℝ) ^ 2) {y}) ∧
    (∀ y g, X.φ g ≠ 0 → τ y * Real.exp (-(1 / (X.I.f : ℝ)) * ∑ v, cartanDistance (X.I.ε v) (g.1 v)) ≤ τ (y * g)) ∧
    ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∀ x, ∃ c : ℝ, 0 < c ∧ ∀ m ∈ X.I.NA W, c ≤ τ (m * x)

def NullStep : Prop :=
  ∀ Z : Set X.I.GA, X.μ Z = 0 → ∀ ν : Measure X.I.GA, IsFiniteMeasure ν →
    ∀ᵐ x ∂(cu_mu X), ∀ᵐ p ∂(ν.prod (cu_mu X)), X.I.rep X.fund (p.1 * x * p.2) ∉ Z

def FinStep : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → FiniteDimensional ℂ (X.rg T)

end cu

theorem cu_inv_rep (X : CData) (τ : X.I.GA → ℝ) (hinv : ∀ γ ∈ X.I.GFset, ∀ y, τ (γ * y) = τ y) (z : X.I.GA) :
    τ (X.I.rep X.fund z) = τ z := by
  unfold AutInst.rep
  split_ifs with h
  · exact hinv _ h.choose_spec.1 z
  · rfl

theorem cu_Act_le (X : CData) {t c S : ℝ} (hc : 0 < c) (ht : c * Real.exp (-(1 / (X.I.f : ℝ)) * S) ≤ t) :
    cu.Act X t ≤ cu.Act X c * Real.exp (2 * (X.I.n : ℝ) ^ 2 * S) ^ 2 := by
  have hf : (0 : ℝ) < (X.I.f : ℝ) := by exact_mod_cast one_le_autInst_f X.I
  set u : ℝ := Real.exp (-(1 / (X.I.f : ℝ)) * S) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hcu : 0 < c * u := mul_pos hc hu0
  have h1 : 3 * Real.sqrt (X.I.n : ℝ) / t ^ 2 ≤ 3 * Real.sqrt (X.I.n : ℝ) / c ^ 2 * (1 / u ^ 2) := by
    have e : 3 * Real.sqrt (X.I.n : ℝ) / c ^ 2 * (1 / u ^ 2) = 3 * Real.sqrt (X.I.n : ℝ) / (c * u) ^ 2 := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hcu.le ht 2
  unfold cu.Act
  refine le_trans (pow_le_pow_left₀ (by have := lt_of_lt_of_le hcu ht; positivity) h1 _) ?_
  rw [mul_pow]
  refine le_of_eq ?_
  congr 1
  rw [hu, one_div, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem cu_growthStep_of (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)
    (h1 : X.GapAboveThreeHalvesPower) (hE : X.LowProj)
    (hr : ∀ v, 1 ≤ q0At X.I v → 16 * (2 * (X.I.n : ℝ) ^ 2) * Real.sqrt (2 * (q0At X.I v : ℝ)) ≤ X.h)
    (hn : 1 ≤ X.I.n) (hS : cu.SizeStep X) (hN : cu.NullStep X) (hK : X.KernelDiag) (hF : cu.FinStep X) :
    cu.GrowthStep X := by
  intro T hT hP Fv hFv W hW ν hν
  obtain ⟨τ, hτ0, hτinv, hcnt, hlip, hlow⟩ := hS
  have := hF T hT hP
  have hfin := hν.1
  obtain ⟨hq, -⟩ := X.qq_spec hX
  have hp : X.I.IsPosType X.e := hX.1.2.2.2.2.2.2.1.2.2.2.1
  set k0 : ℝ := fdegAll X.I X.σ X.w * (X.e 1).re with hk0
  have hk0n : 0 ≤ k0 := mul_nonneg X.fdegAll_nonneg (X.e_one_nonneg hp)
  set Bc : ℝ := 2 * (X.I.n : ℝ) ^ 2 with hBc
  have hBc0 : 0 < Bc := by
    have : (1 : ℝ) ≤ (X.I.n : ℝ) := by exact_mod_cast hn
    positivity
  set M : ℝ := ∫ z, ‖(Fv : X.I.GA → ℂ) z‖ ^ 2 ∂X.μ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun z => by positivity
  have hKc0 : 0 ≤ cu_Kc X Bc := le_trans zero_le_one (cu_one_le_Kc X hBc0)
  have hAct0 : ∀ t : ℝ, 0 < t → 0 ≤ cu.Act X t := fun t ht => by unfold cu.Act; positivity

  have hb : ∀ᵐ y ∂X.μ, ‖(Fv : X.I.GA → ℂ) y‖ ^ 2 ≤ M * (k0 * (cu.Act X (τ y) * cu_Kc X Bc)) := by
    filter_upwards [cu_range_le_kernel X hK T hT hP Fv hFv] with y hy
    refine le_trans hy.2 (mul_le_mul_of_nonneg_left ?_ hM0)
    have h2 : ‖X.kerD y‖ₑ ≤ ENNReal.ofReal (k0 * (cu.Act X (τ y) * cu_Kc X Bc)) :=
      le_trans enorm_tsum_le_tsum_enorm
        (cu_absS_le X D hdec hX h1 hE hq (hAct0 _ (hτ0 y)) hBc0
          (fun hq1 => by
            obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.I.F))
            have := hr v (by rw [hq v]; exact hq1)
            rwa [hq v] at this) (hcnt y))
    rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0n (mul_nonneg (hAct0 _ (hτ0 y)) hKc0))] at h2
    exact le_trans (Complex.re_le_norm _) h2
  have hZ : X.μ {y | ¬ ‖(Fv : X.I.GA → ℂ) y‖ ^ 2 ≤ M * (k0 * (cu.Act X (τ y) * cu_Kc X Bc))} = 0 := ae_iff.1 hb
  filter_upwards [hN _ hZ ν hfin] with x hx
  obtain ⟨c, hc0, hc⟩ := hlow W hW x
  refine ⟨Real.sqrt (M * (k0 * (cu.Act X c * cu_Kc X Bc))), ?_⟩
  have hmem : ∀ᵐ p ∂(ν.prod (cu_mu X)), p.1 ∈ X.I.NA W := by
    have h3 : ∀ᵐ m ∂ν, m ∈ X.I.NA W := by
      rw [ae_iff]
      exact hν.2.2.1
    exact Measure.quasiMeasurePreserving_fst.ae h3
  filter_upwards [hx, hmem] with p hp1 hp2 hφ
  set S : ℝ := ∑ v, cartanDistance (X.I.ε v) (p.2.1 v) with hSdef
  have hz : ‖(Fv : X.I.GA → ℂ) (X.I.rep X.fund (p.1 * x * p.2))‖ ^ 2 ≤
      M * (k0 * (cu.Act X (τ (X.I.rep X.fund (p.1 * x * p.2))) * cu_Kc X Bc)) := by
    by_contra hcon
    exact hp1 hcon
  rw [cu_inv_rep X τ hτinv] at hz
  have ht : c * Real.exp (-(1 / (X.I.f : ℝ)) * S) ≤ τ (p.1 * x * p.2) :=
    le_trans (mul_le_mul_of_nonneg_right (hc _ hp2) (Real.exp_pos _).le) (hlip _ _ hφ)
  have hA := cu_Act_le X hc0 ht
  have hw : cu_wt X Bc p.2 = Real.exp (Bc * S) := rfl
  have hfin2 : ‖X.I.ext Fv (p.1 * x * p.2)‖ ^ 2 ≤
      (Real.sqrt (M * (k0 * (cu.Act X c * cu_Kc X Bc))) * cu_wt X Bc p.2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hM0 (mul_nonneg hk0n (mul_nonneg (hAct0 _ hc0) hKc0))), hw]
    refine le_trans hz ?_
    calc M * (k0 * (cu.Act X (τ (p.1 * x * p.2)) * cu_Kc X Bc))
        ≤ M * (k0 * ((cu.Act X c * Real.exp (Bc * S) ^ 2) * cu_Kc X Bc)) := by gcongr
      _ = M * (k0 * (cu.Act X c * cu_Kc X Bc)) * Real.exp (Bc * S) ^ 2 := by ring
  exact (abs_le_of_sq_le_sq' hfin2 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).2

namespace cu

variable (X : CData)

def MeasMul : Prop := Measurable fun p : X.I.GA × X.I.GA => p.1 * p.2

def CountGF : Prop := (X.I.GFset).Countable

def ExtMeas : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T, AEStronglyMeasurable (X.I.ext Fv) (cu_mu X)

def ReproAE : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∀ᵐ z ∂(cu_mu X), X.I.ext Fv z = ∫ g, X.I.ext Fv (z * g) * X.φ g ∂(cu_mu X)

end cu

section Gen

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]

theorem cu_gen_qmp (h : Measurable fun p : G × G => p.1 * p.2) (ν : Measure G) [SFinite ν] (x : G) :
    Measure.QuasiMeasurePreserving (fun p : G × G => p.1 * x * p.2) (ν.prod μ) μ := by
  have hm : Measurable (fun p : G × G => p.1 * x * p.2) :=
    h.comp ((h.comp (measurable_fst.prodMk measurable_const)).prodMk measurable_snd)
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.measure_prod_null (hm hs)]
  refine Filter.Eventually.of_forall fun m => ?_
  show μ ((fun g => m * x * g) ⁻¹' s) = 0
  rw [measure_preimage_mul, h0]

theorem cu_gen_qmp' (h : Measurable fun p : G × G => p.1 * p.2) (ν : Measure G) [SFinite ν] :
    Measure.QuasiMeasurePreserving (fun p : G × G => p.2 * p.1) (μ.prod ν) μ := by
  have hm : Measurable (fun p : G × G => p.2 * p.1) := h.comp (measurable_snd.prodMk measurable_fst)
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hm hs)]
  have : ∀ m : G, μ ((fun y => (y, m)) ⁻¹' ((fun p : G × G => p.2 * p.1) ⁻¹' s)) = 0 := by
    intro m
    show μ ((fun g => m * g) ⁻¹' s) = 0
    rw [measure_preimage_mul, h0]
  simp only [this, lintegral_zero]

end Gen

theorem cu_qmp (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (ν : Measure X.I.GA) [SFinite ν]
    (x : X.I.GA) :
    Measure.QuasiMeasurePreserving (fun p : X.I.GA × X.I.GA => p.1 * x * p.2) (ν.prod (cu_mu X)) (cu_mu X) :=
  cu_gen_qmp (cu_mu X) hmul ν x

theorem cu_qmp' (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (ν : Measure X.I.GA) [SFinite ν] :
    Measure.QuasiMeasurePreserving (fun p : X.I.GA × X.I.GA => p.2 * p.1) ((cu_mu X).prod ν) (cu_mu X) :=
  cu_gen_qmp' (cu_mu X) hmul ν

theorem cu_rep_avoid (X : CData) (hL : (cu_mu X).IsMulLeftInvariant) (hc : cu.CountGF X)
    (hfd : X.I.IsFundDom (cu_mu X) X.fund) (Z : Set X.I.GA) (hZ : X.μ Z = 0) :
    ∀ᵐ z ∂(cu_mu X), X.I.rep X.fund z ∉ Z := by
  have hZ' : cu_mu X (Z ∩ X.fund) = 0 := by
    have : X.μ Z = cu_mu X (Z ∩ X.fund) := Measure.restrict_apply' hfd.1
    rw [← this, hZ]
  have hU : cu_mu X (⋃ γ ∈ X.I.GFset, (fun z => γ * z) ⁻¹' (Z ∩ X.fund)) = 0 := by
    rw [measure_biUnion_null_iff hc]
    intro γ _
    rw [measure_preimage_mul, hZ']
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_) hU
  simp only [Set.mem_ofPred_eq, not_not] at hz
  have hex := hfd.2.1 z
  unfold AutInst.rep at hz
  rw [dif_pos hex] at hz
  exact Set.mem_biUnion hex.choose_spec.1 ⟨hz, hex.choose_spec.2⟩

theorem cu_nullStep_of (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (hc : cu.CountGF X)
    (hfd : X.I.IsFundDom (cu_mu X) X.fund) : cu.NullStep X := by
  intro Z hZ ν hν
  exact Filter.Eventually.of_forall fun x => (cu_qmp X hmul hL ν x).ae (cu_rep_avoid X hL hc hfd Z hZ)

theorem cu_measStep_of (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (hE : cu.ExtMeas X) :
    cu.MeasStep X := by
  intro T hT hP Fv hFv W _ ν hν
  have := hν.1
  exact Filter.Eventually.of_forall fun x => (hE T hT hP Fv hFv).comp_quasiMeasurePreserving (cu_qmp X hmul hL ν x)

theorem cu_pointRepro_of (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (hR : cu.ReproAE X) :
    cu.PointRepro X := by
  intro T hT hP Fv hFv W _ ν hν
  have := hν.1
  exact Measure.ae_ae_of_ae_prod ((cu_qmp' X hmul hL ν).ae (hR T hT hP Fv hFv))

namespace cu_NObj

variable {X : CData} (O : cu_NObj X)

def IsWeilNull : Prop :=
  ∀ Z : Set X.I.GA, cu_mu X Z = 0 → ∀ᵐ y ∂O.lam, ∀ᵐ n ∂O.μNA, n * y ∉ Z

def RInv (v : InfinitePlace X.I.F) : Prop :=
  ∀ᵐ n₀ ∂(O.μN v), ∀ F : Formalism.REAL.UJ (X.I.ε v) → ℂ, ∫ n, F (n * n₀) ∂(O.μN v) = ∫ n, F n ∂(O.μN v)

def LocZero (v : InfinitePlace X.I.F) : Prop :=
  ∀ a : Formalism.REAL.UJ (X.I.ε v), ∀ᵐ b ∂(Formalism.REAL.muG (X.I.ε v)),
    ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) (a⁻¹ * (n * b)) ∂(O.μN v) = 0

theorem phPZero_of {v : InfinitePlace X.I.F} (hN : O.IsWeilNull) (h0 : O.μNA ≠ 0) (hR : O.RInv v) (hZ : O.LocZero v)
    (x : X.I.GA) : O.PhPZero x := by
  refine ⟨v, ?_⟩
  set I : Formalism.REAL.UJ (X.I.ε v) → ℂ :=
    fun b => ∫ n, phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n * b)) ∂(O.μN v) with hI
  have q1 : Measure.QuasiMeasurePreserving (fun z : X.I.GA => z.1 v) (cu_mu X) (Formalism.REAL.muG (X.I.ε v)) :=
    (Measure.quasiMeasurePreserving_eval (μ := fun v => Formalism.REAL.muG (X.I.ε v)) v).comp
      Measure.quasiMeasurePreserving_fst
  have q2 : Measure.QuasiMeasurePreserving (fun z : X.I.GA => z.1 v) O.μNA (O.μN v) :=
    (Measure.quasiMeasurePreserving_eval (μ := O.μN) v).comp Measure.quasiMeasurePreserving_fst
  have hB : cu_mu X {z : X.I.GA | ¬ I (z.1 v) = 0} = 0 := ae_iff.1 (q1.ae (hZ (x.1 v)))
  have hR' : ∀ᵐ n ∂O.μNA, ∀ F : Formalism.REAL.UJ (X.I.ε v) → ℂ,
      ∫ n', F (n' * n.1 v) ∂(O.μN v) = ∫ n', F n' ∂(O.μN v) := q2.ae hR
  have : (ae O.μNA).NeBot := ae_neBot.2 h0
  filter_upwards [hN _ hB] with y hy
  obtain ⟨n, hn1, hn2⟩ := (hy.and hR').exists
  have e1 : I (n.1 v * y.1 v) = 0 := by
    by_contra hcon
    exact hn1 hcon
  have e2 := hn2 fun n' => phLoc (X.I.ε v) (X.σ v) (X.w v) ((x.1 v)⁻¹ * (n' * y.1 v))
  show I (y.1 v) = 0
  rw [← e1]
  simp only [hI]
  rw [← e2]
  simp only [mul_assoc]

end cu_NObj

namespace cu

variable (X : CData)

def ExtInv : Prop :=
  ∀ T : X.L2 →L[ℂ] X.L2, X.IsOp T → IsStarProjection T → ∀ Fv ∈ X.rg T,
    ∃ f' : X.I.GA → ℂ, (∀ γ ∈ X.I.GFset, ∀ y, f' (γ * y) = f' y) ∧ X.I.ext Fv =ᵐ[cu_mu X] f'

def UnipFine : Prop :=
  ∀ W : Submodule X.I.E (Fin X.I.n → X.I.E), X.I.IsIsot W → ∃ O : cu_NObj X, O.IsOn W ∧ O.IsWeil ∧ O.IsWeilNull ∧
    O.μNA ≠ 0 ∧ ∃ v, O.RInv v ∧ O.LocZero v

end cu

theorem cu_cstInv_of (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant)
    {W : Submodule X.I.E (Fin X.I.n → X.I.E)} {ν : Measure X.I.GA} (hν : X.I.IsNQuotMeas W ν) (O : cu_NObj X)
    (hOn : O.IsOn W) (hN : O.IsWeilNull) {f f' : X.I.GA → ℂ} (hinv : ∀ γ ∈ X.I.GFset, ∀ y, f' (γ * y) = f' y)
    (hff : f =ᵐ[cu_mu X] f') : O.CstInv ν f := by
  have := hν.1

  have h1 : ∀ᵐ y ∂(cu_mu X), cu_cst X ν f y = cu_cst X ν f' y := by
    have h2 : ∀ᵐ y ∂(cu_mu X), ∀ᵐ m ∂ν, f (m * y) = f' (m * y) :=
      Measure.ae_ae_of_ae_prod ((cu_qmp' X hmul hL ν).ae hff)
    exact h2.mono fun y hy => integral_congr_ae hy

  have h3 : ∀ n ∈ X.I.NA W, ∀ y, cu_cst X ν f' (n * y) = cu_cst X ν f' y := by
    intro n hn y
    have := hν.2.2.2 (fun m => f' (m * y)) (fun γ hγ m => by rw [mul_assoc]; exact hinv γ hγ.1 _) n hn
    unfold cu_cst
    rw [← this]
    simp only [mul_assoc]
  have h4 : ∀ᵐ n ∂O.μNA, n ∈ X.I.NA W := by
    rw [ae_iff]
    exact hOn
  filter_upwards [hN _ (ae_iff.1 h1)] with y hy
  refine ⟨cu_cst X ν f' y, ?_⟩
  filter_upwards [hy, h4] with n hn1 hn2
  have : cu_cst X ν f (n * y) = cu_cst X ν f' (n * y) := by
    by_contra hcon
    exact hn1 hcon
  rw [this, h3 n hn2 y]

theorem cu_unipStep_of (X : CData) (hmul : cu.MeasMul X) (hL : (cu_mu X).IsMulLeftInvariant) (hU : cu.UnipFine X)
    (hI : cu.ExtInv X) : cu.UnipStep X := by
  intro W hW
  obtain ⟨O, hOn, hWeil, hNull, h0, v, hR, hZ⟩ := hU W hW
  refine ⟨O, hOn, hWeil, fun x => O.phPZero_of hNull h0 hR hZ x, fun T hT hP Fv hFv ν hν => ?_⟩
  obtain ⟨f', hinv, hff⟩ := hI T hT hP Fv hFv
  exact cu_cstInv_of X hmul hL hν O hOn hNull hinv hff

namespace cu

def Fine (X : CData) : Prop :=
  UnipFine X ∧ HaarGrowth X ∧ SizeStep X ∧ X.KernelDiag ∧ ReproAE X ∧ ExtInv X ∧ ExtMeas X ∧ MeasMul X ∧ CountGF X

end cu

theorem cuspidal_range_of_fine_facts (X : CData) (D : Formalism.BasicNotions.D7) (hdec : DiscreteSeriesDecayBound D) {n₀ : ℕ} {A C : ℝ} (hn₀ : 1 ≤ n₀)
    (hC : 46 ≤ C) (hX : X.HypB n₀ A) (h1 : X.GapAboveThreeHalvesPower) (h2 : X.GapAboveSquareRootThreshold C) (hE : X.LowProj) (hF : cu.FinStep X)
    (hS : cu.Fine X) : X.CuspStep := by
  obtain ⟨sU, sH, sS, sK, sR, sI, sE, sM, sC⟩ := hS
  have hf : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  have hfd : X.I.IsFundDom (cu_mu X) X.fund := hX.2.1.2.2.2.2.1
  have hL := cu_leftInv X hf
  have hn : 1 ≤ X.I.n := le_trans hn₀ hX.1.1
  refine cuspidal_range_of_repro_unipotent X hf
    (cu_reproStep_of X (fun v hq => (cu_thresholds X hC h2 v hq).1) sH
      (cu_growthStep_of X D hdec hX h1 hE (fun v hq => (cu_thresholds X hC h2 v hq).2.1) hn sS
        (cu_nullStep_of X sM hL sC hfd) sK hF)
      (cu_measStep_of X sM hL sE) (cu_pointRepro_of X sM hL sR)) (cu_unipStep_of X sM hL sU sI)

def cu_StepsCusp (n₀ : ℕ) (A C : ℝ) : Prop :=
  ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → cu.Fine X

theorem projection_facts_of_fine (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C : ℝ) (hn₀ : 1 ≤ n₀) (hC : 46 ≤ C) (ha2 : adm2 D)
    (ha8 : adm8 D) (hdec : DiscreteSeriesDecayBound D)
    (hPC : ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold C → X.ProjStep ∧ X.CountedStep)
    (hcu : cu_StepsCusp n₀ A C) : StepsB n₀ A C := by
  intro X hX h1 h2
  obtain ⟨s1, s2⟩ := hPC X hX h1 h2
  refine ⟨s1, s2, cuspidal_range_of_fine_facts X D hdec hn₀ hC hX h1 h2 (lowest_K_type_projector_exists D ha2 X hX) ?_ (hcu X hX h1 h2)⟩
  intro T hT hP
  obtain ⟨κ, -⟩ := s2 T hT hP
  have hfd : FiniteDimensional ℂ (X.I.eHom X.σs X.μf X.fund X.R X.Re) :=
    ha8 X.I n₀ A X.b X.lam X.g X.g₀ X.e X.H X.σ X.w X.Hs X.σs X.tens X.μf X.fund X.R X.Re hX.1 hX.2.1
  exact Module.Finite.equiv κ

theorem projection_statement_of_fine (D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A Cb : ℝ) (hn₀ : 1 ≤ n₀) (hC : 46 ≤ Cb) (ha2 : adm2 D)
    (hPC : ∀ X : CData, X.HypB n₀ A → X.GapAboveThreeHalvesPower → X.GapAboveSquareRootThreshold Cb → X.ProjStep ∧ X.CountedStep)
    (hcu : cu_StepsCusp n₀ A Cb) : HodgeTateFromSandwich D n₀ A Cb :=
  hodgeTateFromSandwich_of_admissibility_implication D n₀ A Cb fun hadm hdec _ => projection_facts_of_fine D n₀ A Cb hn₀ hC ha2 hadm.2.2 hdec hPC hcu

end Formalism.MainNotions.LeviCoordinates
