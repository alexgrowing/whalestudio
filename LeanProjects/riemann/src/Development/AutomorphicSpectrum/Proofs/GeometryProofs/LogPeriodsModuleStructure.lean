import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction

open GroundTheory.Heights₂.Heights.Regular

theorem exists_eventually_int_eq_zero {X V J : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fintype J] (v : X → J → V) (x₀ : X)
    (hv : ∀ i, ContinuousAt (fun x => v x i) x₀)
    (hind : ∀ r : J → ℝ, ∑ i, r i • v x₀ i = 0 → r = 0) :
    ∃ ε > (0 : ℝ), ∀ᶠ x in 𝓝 x₀, ∀ m : J → ℤ, ‖∑ i, (m i : ℝ) • v x i‖ < ε → m = 0 := by
  classical
  let T : (J → ℝ) →ₗ[ℝ] V := ∑ i, (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).smulRight (v x₀ i)
  have hT : ∀ r, T r = ∑ i, r i • v x₀ i := fun r => by simp [T, LinearMap.sum_apply]
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    exact hind r (by rw [← hT]; exact hr)
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hb : ∀ r, ‖r‖ ≤ K * ‖T r‖ := fun r => by
    simpa [dist_zero_right] using hK.le_mul_dist r 0
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card J + 1 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * K * N) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖v x i - v x₀ i‖ < δ := by
    refine eventually_all.2 fun i => ?_
    have := (Metric.tendsto_nhds.1 (hv i).tendsto) δ hδ
    simpa [dist_eq_norm] using this
  filter_upwards [hev] with x hx m hm
  obtain ⟨r, hr⟩ : ∃ r : J → ℝ, r = fun i => (m i : ℝ) := ⟨_, rfl⟩
  have hm' : ‖∑ i, r i • v x i‖ < 1 / (2 * K) := by rw [hr]; exact hm
  have hsplit : T r = ∑ i, r i • v x i - ∑ i, r i • (v x i - v x₀ i) := by
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]; abel
  have herr : ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ N * (‖r‖ * δ) := by
    calc ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ ∑ i, ‖r i • (v x i - v x₀ i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : J, ‖r‖ * δ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm r i) (hx i).le (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card J : ℝ) * (‖r‖ * δ) := by simp
      _ ≤ N * (‖r‖ * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hNdef]; linarith
  have h1 : ‖r‖ ≤ K * (‖∑ i, r i • v x i‖ + N * (‖r‖ * δ)) := by
    refine (hb r).trans (mul_le_mul_of_nonneg_left ?_ hKpos.le)
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith)
  have h2 : K * (N * (‖r‖ * δ)) = ‖r‖ / 2 := by
    rw [hδdef]; field_simp
  have h3 : K * ‖∑ i, r i • v x i‖ < 1 / 2 := by
    have := mul_lt_mul_of_pos_left hm' hKpos
    have h4 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
    linarith
  have h5 : ‖r‖ < 1 := by
    rw [mul_add, h2] at h1
    linarith
  funext i
  have h6 : |(m i : ℝ)| < 1 := by
    have := (norm_le_pi_norm r i).trans_lt h5
    rw [hr] at this
    simpa [Real.norm_eq_abs] using this
  have h7 : |m i| < 1 := by exact_mod_cast h6
  simpa using Int.abs_lt_one_iff.1 h7

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)

theorem P_injective {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  rw [map_zero]
  refine LinearMap.ext fun y => ?_
  have h := L.im w hw x y
  rw [hx] at h
  simp at h
  exact_mod_cast h.symm

theorem real_indep {J : Type*} [Fintype J] (b : Module.Basis J ℤ Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (r : J → ℝ) (h : ∑ i, r i • L.P w (b i) = 0) : r = 0 := by
  classical
  funext j
  obtain ⟨u, hu⟩ := L.unimod.2 (b.coord j)
  let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star v).im
      map_add' := fun v v' => by simp [star_add, mulVec_add, dotProduct_add]
      map_smul' := fun t v => by simp [star_smul, mulVec_smul, dotProduct_smul] }
  have h1 : ∀ i, ψ (L.P w (b i)) = if i = j then 1 else 0 := fun i => by
    have h2 := L.im w hw u (b i)
    change (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w (b i))).im = _
    rw [h2, hu]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have h2 := congrArg ψ h
  simp only [map_sum, map_smul, h1, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simpa using h2

theorem continuousAt_P (x : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => L.P w x) w₀ :=
  (L.hol x).continuousOn.continuousAt ((isOpen_logCover L.a_le).mem_nhds hw)

theorem continuousAt_apply (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1)) (x : Λ)
    {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => A (expCover a w) (L.P w x)) w₀ := by
  classical
  have hP := continuousAt_P L x hw
  have hexp : ContinuousAt (expCover (n := n) a) w₀ := (continuous_expCover a).continuousAt
  have hAe : ∀ v, ContinuousAt (fun w => A (expCover a w) v) w₀ := fun v =>
    ContinuousAt.comp (f := expCover a) (g := fun z => A z v)
      ((hA v).continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (expCover_mem_ball L.a_le hw))) hexp
  have h1 : (fun w => A (expCover a w) (L.P w x)) = fun w =>
      ∑ i, (L.P w x i) • A (expCover a w) (fun j => if i = j then 1 else 0) := by
    funext w
    exact LinearMap.pi_apply_eq_sum_univ _ _
  rw [h1]
  exact tendsto_finset_sum _ fun i _ =>
    (((continuous_apply i).continuousAt.comp hP).smul (hAe _))

theorem eventually_eq (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    ∀ᶠ w in 𝓝 w₀, L.P w y = A (expCover a w) (L.P w x) := by
  haveI := L.free
  haveI := L.fin
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ) :=
    ⟨Module.Free.chooseBasis ℤ Λ⟩
  obtain ⟨ε, hε, hev⟩ := exists_eventually_int_eq_zero (fun w i => L.P w (b i)) w₀
    (fun i => continuousAt_P L (b i) hw) (real_indep L b hw)
  have hD : ContinuousAt (fun w => A (expCover a w) (L.P w x) - L.P w y) w₀ :=
    (continuousAt_apply L A hA x hw).sub (continuousAt_P L y hw)
  have hsmall : ∀ᶠ w in 𝓝 w₀, ‖A (expCover a w) (L.P w x) - L.P w y‖ < ε := by
    have h0 := (Metric.tendsto_nhds.1 hD.tendsto) ε hε
    simpa [h, dist_eq_norm] using h0
  filter_upwards [hev, hsmall, (isOpen_logCover L.a_le).mem_nhds hw] with w h1 h2 hwC
  obtain ⟨y', hy'⟩ := hex w hwC x
  have hk : L.P w (y' - y) = ∑ i, ((b.repr (y' - y) i : ℤ) : ℝ) • L.P w (b i) := by
    conv_lhs => rw [← b.sum_repr (y' - y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  have hm := h1 (fun i => b.repr (y' - y) i) (by rw [← hk, map_sub, hy']; exact h2)
  have h0 : y' - y = 0 := b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun hm i)
  rw [← sub_eq_zero.1 h0, hy']

theorem eq_of_mem (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ w₁ : Fin n → ℂ} (h0 : w₀ ∈ logCover L.a_le) (h1 : w₁ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    L.P w₁ y = A (expCover a w₁) (L.P w₁ x) := by
  classical
  choose φ hφ using fun w : logCover L.a_le => hex w.1 w.2 x
  have hlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have h2 := (continuous_subtype_val.continuousAt (x := w)).eventually
      (eventually_eq L A hA hex x (φ w) w.2 (hφ w))
    filter_upwards [h2] with w' hw'
    exact P_injective L w'.2 ((hφ w').trans hw'.symm)
  haveI : PreconnectedSpace (logCover L.a_le) :=
    Subtype.preconnectedSpace (convex_logCover L.a_le).isPreconnected
  have h2 := hlc.apply_eq_of_preconnectedSpace ⟨w₀, h0⟩ ⟨w₁, h1⟩
  have hy : φ ⟨w₀, h0⟩ = y := P_injective L h0 ((hφ ⟨w₀, h0⟩).trans h.symm)
  rw [← hy, h2]
  exact hφ ⟨w₁, h1⟩

theorem exists_module_of_period_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  intro E _ _ _ n a g Λ _ L B hB hex
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty L.a_le
  choose f hf using fun c x => hex w₀ hw₀ c x
  have key : ∀ w ∈ logCover L.a_le, ∀ c x, L.P w (f c x) = B (expCover a w) c (L.P w x) :=
    fun w hw c x => eq_of_mem L (fun z => B z c) (fun x => hB c x)
      (fun w hw x => hex w hw c x) x (f c x) hw₀ hw (hf c x)
  have inj := P_injective L hw₀
  have e1 : ∀ x, f 1 x = x := fun x => inj (by rw [hf]; simp)
  have e2 : ∀ c d x, f (c * d) x = f c (f d x) := fun c d x => inj (by
    rw [hf, hf, hf, map_mul, Module.End.mul_apply])
  have e3 : ∀ c, f c 0 = 0 := fun c => inj (by rw [hf]; simp)
  have e4 : ∀ c x y, f c (x + y) = f c x + f c y := fun c x y => inj (by
    rw [map_add, hf, hf, hf, map_add, map_add])
  have e5 : ∀ c d x, f (c + d) x = f c x + f d x := fun c d x => inj (by
    rw [map_add, hf, hf, hf, map_add, LinearMap.add_apply])
  have e6 : ∀ x, f 0 x = 0 := fun x => inj (by rw [hf]; simp)
  exact ⟨{ smul := f, one_smul := e1, mul_smul := e2, smul_zero := e3, smul_add := e4,
           add_smul := e5, zero_smul := e6 }, key⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction
