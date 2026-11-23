import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralTailBoundExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralContinuityEstimateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopIntersectionDifferenceFormula

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

noncomputable section

namespace GlobalTheory.Mean4O.Cauchy

theorem levi_add_divisor {e : ℕ} {f g : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (w : Fin e → ℂ) : levi (fun x => f x + g x) z w = levi f z w + levi g z w := by
  have h1 : fderiv ℝ (fun x => f x + g x) =ᶠ[𝓝 z] fun x => fderiv ℝ f x + fderiv ℝ g x := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with x hx hy
    exact fderiv_fun_add (hx.differentiableAt (by norm_num)) (hy.differentiableAt (by norm_num))
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (fderiv ℝ g) z :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold levi
  rw [h1.fderiv_eq, fderiv_fun_add hf' hg']
  simp only [add_apply]
  ring

theorem levi_const_mul_divisor {e : ℕ} {f : (Fin e → ℂ) → ℝ} {z : Fin e → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f z)
    (w : Fin e → ℂ) : levi (fun x => c * f x) z w = c * levi f z w := by
  have h1 : fderiv ℝ (fun x => c * f x) =ᶠ[𝓝 z] fun x => c • fderiv ℝ f x := by
    filter_upwards [hf.eventually (by simp)] with x hx
    exact fderiv_const_mul (hx.differentiableAt (by norm_num)) c
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold levi
  rw [h1.fderiv_eq, fderiv_fun_const_smul hf']
  simp only [smul_apply, smul_eq_mul]
  ring

section One

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

def Loc (A : FinHolAtlas e X) (P : LocPot X) : Prop :=
  ∀ j, ∀ y ∈ (A.chart j).target, ContDiffAt ℝ 2 (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y

theorem contDiffAt_of_smoothOn {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hy' : (A.chart j).symm y ∈ U) :
    ContDiffAt ℝ 2 (f ∘ (A.chart j).symm) y := by
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) := (A.chart j).isOpen_inter_preimage_symm hU
  exact ((hf j).contDiffAt (ho.mem_nhds ⟨hy, hy'⟩)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

theorem loc_pot {P : LocPot X} (h : IsPotential A P) : Loc A P := fun j _ hy =>
  contDiffAt_of_smoothOn (P.isOpen_U _) (h.1 _) j hy (P.mem_U _)

theorem loc_fun {f : X → ℝ} (h : A.Smooth f) : Loc A (LocPot.ofFun f) := fun j _ hy =>
  contDiffAt_of_smoothOn isOpen_univ h j hy (Set.mem_univ _)

theorem loc_add {P Q : LocPot X} (hP : Loc A P) (hQ : Loc A Q) : Loc A (P + Q) := fun j y hy =>
  (hP j y hy).add (hQ j y hy)

theorem loc_rsmul {P : LocPot X} (c : ℝ) (hP : Loc A P) : Loc A (P.rsmul c) := fun j y hy =>
  contDiffAt_const.mul (hP j y hy)

theorem leviAt_add {P Q : LocPot X} (hP : Loc A P) (hQ : Loc A Q) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w :=
  levi_add_divisor (hP j y hy) (hQ j y hy) w

theorem leviAt_rsmul {P : LocPot X} (c : ℝ) (hP : Loc A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : leviAt A (P.rsmul c) j y w = c * leviAt A P j y w :=
  levi_const_mul_divisor c (hP j y hy) w

theorem continuous_of_smooth {f : X → ℝ} (h : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (contDiffAt_of_smoothOn isOpen_univ h j ((A.chart j).map_source hj) (Set.mem_univ _)).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

theorem smooth_sub {f g : X → ℝ} (hf : A.Smooth f) (hg : A.Smooth g) : A.Smooth (f - g) := fun j =>
  (hf j).sub (hg j)

theorem comb_of_leviEq {Z : Set X} {r : X → ℝ} {Om : LocPot X} {K : ℝ} {P Q : LocPot X} (hP : IsPotential A P)
    (h : LeviEq A P Q) (hQ : Comb A Z r Om K Q) : Comb A Z r Om K P := by
  obtain ⟨-, T, c, h1, h2⟩ := hQ
  exact ⟨hP, T, c, h1, fun j y hy hz w => (h j y hy w).trans (h2 j y hy hz w)⟩

end One

theorem first_chern_form_levi_sum {e : ℕ} {M : Man e} (K : Calc M) (v a : K.V) (s : ℝ) (g : M.Fun) (hg : M.Smooth g) (σ : Fin (M.n + 1))
    {P Q : LocPot (M.X σ)} (hP : IsPotential (M.A σ) P) (hQ : IsPotential (M.A σ) Q)
    (hv : LeviEq (M.A σ) (K.c1 v σ) P) (ha : LeviEq (M.A σ) (K.c1 a σ) Q) :
    LeviEq (M.A σ) (K.c1 (v + s • a + K.ar g) σ) (P + Q.rsmul s + LocPot.ofFun (g σ)) := by
  intro j y hy w
  have l := fun x => loc_pot (K.firstChern_isPotential x σ)
  rw [K.isOneCochain_add _ _ σ j y hy w, leviAt_add (l _) (l _) j hy, K.isOneCochain_add _ _ σ j y hy w, leviAt_add (l _) (l _) j hy,
    K.firstChern_smul_leviEq _ _ σ j y hy w, leviAt_rsmul _ (l _) j hy, K.c1_ar g hg σ j y hy w, hv j y hy w, ha j y hy w,
    leviAt_add (loc_add (loc_pot hP) (loc_rsmul _ (loc_pot hQ))) (loc_fun (hg σ)) j hy,
    leviAt_add (loc_pot hP) (loc_rsmul _ (loc_pot hQ)) j hy, leviAt_rsmul _ (loc_pot hQ) j hy]

theorem top_sub_le {e : ℕ} {M : Man e} (K : Calc M) (v : K.V) (g g' : M.Fun) (hg : M.Smooth g) (hg' : M.Smooth g')
    (S : ∀ σ, LocPot (M.X σ) → Prop) (h1 : ∀ σ, S σ (K.c1 (v + K.ar g) σ)) (h2 : ∀ σ, S σ (K.c1 (v + K.ar g') σ))
    (b : Fin (M.n + 1) → ℝ)
    (hb : ∀ σ (P : Fin e → LocPot (M.X σ)), (∀ i, S σ (P i)) → |mInt (M.A σ) P (g' σ - g σ)| ≤ b σ) :
    |K.top (v + K.ar g) - K.top (v + K.ar g')| ≤ (e + 1 : ℝ) * (M.κ * ∑ σ, b σ) := by
  have hs : M.Smooth (g' - g) := fun σ => smooth_sub (hg' σ) (hg σ)
  have e1 : v + K.ar g + K.ar (g' - g) = v + K.ar g' := by rw [map_sub]; abel
  have h := GlobalTheory.Mean4O.top_add_ar_sub e M K (v + K.ar g) (g' - g) hs
  rw [e1] at h
  rw [abs_sub_comm, h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (M.κ * ∑ σ, b σ) ?_).trans (by simp)
  intro i _
  unfold Man.int
  rw [abs_mul, abs_of_pos M.κ_pos]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => ?_)) M.κ_pos.le
  refine hb σ _ fun l => ?_
  by_cases hl : (l : ℕ) < i
  · simpa [hl] using h2 σ
  · simpa [hl] using h1 σ

theorem rate_le (e : ℕ) {K C R : ℝ} (hK : 0 ≤ K) (hR : Real.exp 2 ≤ R) :
    2 * K / R * C + 2 * K * (C * Real.log (Real.sqrt R) ^ (e + 1) / Real.sqrt R) ≤
      4 * K * |C| * (Real.log R ^ (e + 1) / Real.sqrt R) := by
  have h1 : (1 : ℝ) ≤ R := le_trans (Real.one_le_exp (by norm_num)) hR
  have h0 : 0 < R := by linarith
  have hl : 2 ≤ Real.log R := by rw [Real.le_log_iff_exp_le h0]; exact hR
  have hs0 : 0 < Real.sqrt R := Real.sqrt_pos.2 h0
  have hs1 : Real.sqrt R ≤ R := by
    rw [Real.sqrt_le_left h0.le]; nlinarith
  have hp : 1 ≤ Real.log R ^ (e + 1) := one_le_pow₀ (by linarith)
  have a1 : 1 / R ≤ Real.log R ^ (e + 1) / Real.sqrt R := div_le_div₀ (by linarith) hp hs0 hs1
  have a2 : Real.log (Real.sqrt R) ^ (e + 1) / Real.sqrt R ≤ Real.log R ^ (e + 1) / Real.sqrt R := by
    rw [Real.log_sqrt h0.le]
    gcongr
    linarith
  have a3 : 0 ≤ Real.log (Real.sqrt R) ^ (e + 1) / Real.sqrt R := by
    rw [Real.log_sqrt h0.le]; positivity
  have b1 : C * (1 / R) ≤ |C| * (Real.log R ^ (e + 1) / Real.sqrt R) :=
    mul_le_mul (le_abs_self C) a1 (by positivity) (abs_nonneg C)
  have b2 : C * (Real.log (Real.sqrt R) ^ (e + 1) / Real.sqrt R) ≤ |C| * (Real.log R ^ (e + 1) / Real.sqrt R) :=
    mul_le_mul (le_abs_self C) a2 a3 (abs_nonneg C)
  have c1 := mul_le_mul_of_nonneg_left (add_le_add b1 b2) (show 0 ≤ 2 * K by linarith)
  calc _ = 2 * K * (C * (1 / R) + C * (Real.log (Real.sqrt R) ^ (e + 1) / Real.sqrt R)) := by ring
    _ ≤ _ := c1
    _ = _ := by ring

theorem cauchy_rate : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y), (∀ c, (T.F c).FamR Y.j) → ∀ Λ : ℝ, ∃ C : ℝ, ∀ (B : ℝ) (c : Y.Comp) (u : Wt Y), DomL Y.j u → ‖u‖ ≤ Λ → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ R R' : ℝ, Real.exp 2 ≤ R → R ≤ R' → |T.fR B c u s R - T.fR B c u s R'| ≤ C * Real.log R ^ (dimY Y + 1) / Real.sqrt R := by
  intro D Y T hF Λ
  choose K hK using fun c => hF c Λ
  choose C hC using fun c σ => GlobalTheory.T.mixed_integral_tail_bound_exists _ _ ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ)
    ((T.M c).bd σ) (K c)
  let G : Y.Comp → ℝ := fun c =>
    (dimY Y + 1 : ℝ) * ((T.M c).κ * ∑ σ, (3 * K c) ^ dimY Y * (4 * K c * |C c σ|))
  refine ⟨∑ c, |G c|, fun B c u hu hΛ s hs R R' hR hR' => ?_⟩
  have hR2 : Real.exp 2 ≤ R' := hR.trans hR'
  have h0 : 0 < R := lt_of_lt_of_le (Real.exp_pos _) hR
  have hl : 2 ≤ Real.log R := by rw [Real.le_log_iff_exp_le h0]; exact hR
  have k1 := hK c u hu hΛ s hs R hR
  have k2 := hK c u hu hΛ s hs R' hR2
  have hK0 : 0 ≤ K c := by
    obtain ⟨-, ⟨-, _, _, h, -⟩, -⟩ := k1 0
    exact (abs_nonneg _).trans (h 0).2
  have hq : 0 ≤ Real.log R ^ (dimY Y + 1) / Real.sqrt R := by positivity
  have hsq : Real.exp 1 ≤ Real.sqrt R := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← Real.exp_nat_mul]; simpa using hR
  have hc : ∀ R₁, Real.exp 2 ≤ R₁ → ∀ σ, Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) (K c)
      ((T.K B c).c1 (T.L B c u + s • T.a B c + (T.K B c).ar ((T.F c).phR R₁ u)) σ) := fun R₁ h₁ σ =>
    comb_of_leviEq ((T.K B c).firstChern_isPotential _ σ)
      (first_chern_form_levi_sum _ _ _ s _ (fun σ => (hK c u hu hΛ s hs R₁ h₁ σ).1) σ (T.th_pot c u σ) (T.a_pot c σ)
        (T.c1_L B c u σ) (T.firstChern_leviEq_constant B c σ)) (hK c u hu hΛ s hs R₁ h₁ σ).2.1
  have main := top_sub_le (T.K B c) (T.L B c u + s • T.a B c) ((T.F c).phR R u) ((T.F c).phR R' u)
    (fun σ => (k1 σ).1) (fun σ => (k2 σ).1) _ (hc R hR) (hc R' hR2)
    (fun σ => (3 * K c) ^ dimY Y * (4 * K c * |C c σ|) * (Real.log R ^ (dimY Y + 1) / Real.sqrt R)) (by
      intro σ P hP
      have h := GlobalTheory.T.mixed_integral_continuity_estimate _ _ _ _ _ _ ((T.M c).bd σ) (K c) (C c σ) hK0 (hC c σ) P
        ((T.F c).phR R' u σ - (T.F c).phR R u σ) (2 * K c / R) (2 * K c) (Real.sqrt R) hP
        (continuous_of_smooth (smooth_sub (k2 σ).1 (k1 σ).1)) (by positivity) (by positivity) hsq
        (fun x hx hr => by
          have a1 := ((k1 σ).2.2 x hx).2 hr
          have a2 := ((k2 σ).2.2 x hx).2 (hr.trans (Real.sqrt_le_sqrt hR'))
          have a3 : K c / R' ≤ K c / R := div_le_div_of_nonneg_left hK0 h0 hR'
          have a4 : 2 * K c / R = K c / R + K c / R := by ring
          rw [abs_le] at a1 a2 ⊢
          rw [Pi.sub_apply]
          constructor <;> linarith [a1.1, a1.2, a2.1, a2.2])
        (fun x hx _ => by
          have a1 := ((k1 σ).2.2 x hx).1
          have a2 := ((k2 σ).2.2 x hx).1
          rw [abs_le] at a1 a2 ⊢
          rw [Pi.sub_apply]
          constructor <;> linarith [a1.1, a1.2, a2.1, a2.2])
      refine h.trans ?_
      exact (mul_le_mul_of_nonneg_left (rate_le (C := C c σ) (dimY Y) hK0 hR)
        (pow_nonneg (show 0 ≤ 3 * K c by linarith) (dimY Y))).trans_eq (mul_assoc _ _ _).symm)
  have hG : G c ≤ ∑ c, |G c| :=
    (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |G c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
  calc _ ≤ _ := main
    _ = G c * (Real.log R ^ (dimY Y + 1) / Real.sqrt R) := by
        simp only [G, ← Finset.sum_mul]; ring
    _ ≤ (∑ c, |G c|) * (Real.log R ^ (dimY Y + 1) / Real.sqrt R) := mul_le_mul_of_nonneg_right hG hq
    _ = _ := by ring

end GlobalTheory.Mean4O.Cauchy
