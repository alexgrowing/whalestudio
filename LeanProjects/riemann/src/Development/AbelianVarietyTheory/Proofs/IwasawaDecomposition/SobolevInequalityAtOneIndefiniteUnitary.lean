import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevIteratedOneParameterSubgroups
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyBallSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.SobolevHaar

theorem cube_step {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ)
    (c : Fin (N + 1) → ℝ → G) (s : ℝ) (hs : 0 < s)
    (hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b)
    (f f' : G → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun t => f (x * c (Fin.last N) t)) (f' x) 0) :
    ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2 ≤
      2 / s * (∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f (List.ofFn fun i => c i (t i)).prod‖ ^ 2) +
      2 * s * ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖f' (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := by
  set l := Fin.last N with hl
  have hΘ := continuous_prod_ofFn_curves (N + 1) c (fun i => (hc i).1)
  have hΘ' := continuous_prod_ofFn_curves N (fun i => c i.castSucc) (fun i => (hc _).1)
  have hsn : ∀ (t : Fin N → ℝ) (r : ℝ),
      (List.ofFn fun i => c i (Fin.snoc (α := fun _ => ℝ) t r i)).prod
        = (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r := by
    intro t r
    rw [List.ofFn_succ']
    simp [hl]
  have fub : ∀ w : G → ℂ, Continuous w →
      IntegrableOn (fun t : Fin N → ℝ => ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2)
        (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) ∧
      ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 =
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∫ r in (0 : ℝ)..s,
        ‖w ((List.ofFn fun i : Fin N => c i.castSucc (t i)).prod * c l r)‖ ^ 2 := by
    intro w hw
    have h := integral_cube_succ_last N s
      (fun t => ‖w (List.ofFn fun i => c i (t i)).prod‖ ^ 2) ((hw.comp hΘ).norm.pow 2)
    simp only [hsn] at h
    simp only [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
    exact h
  obtain ⟨i1, b1⟩ := fub f hf
  obtain ⟨i2, b2⟩ := fub f' hf'
  have pt : ∀ x : G, ‖f x‖ ^ 2 ≤ 2 / s * (∫ r in (0 : ℝ)..s, ‖f (x * c l r)‖ ^ 2)
      + 2 * s * ∫ r in (0 : ℝ)..s, ‖f' (x * c l r)‖ ^ 2 := by
    intro x
    have h := sobolev_endpoint_one_variable ℂ (fun r => f (x * c l r))
      (fun r => f' (x * c l r)) s hs ?_ ?_
    · simpa only [(hc l).2.1, mul_one] using h
    · intro r _
      have h1 : HasDerivAt (fun t => f (x * c l r * c l t)) (f' (x * c l r)) (r - r) := by
        rw [sub_self]; exact hd _
      have h2 := h1.comp_sub_const r r
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [mul_assoc, ← (hc l).2.2, add_sub_cancel]
    · exact (hf'.comp (continuous_const.mul (hc l).1)).continuousOn
  have i0 : IntegrableOn (fun t : Fin N → ℝ =>
      ‖f (List.ofFn fun i : Fin N => c i.castSucc (t i)).prod‖ ^ 2)
      (Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s)) :=
    ((hf.comp hΘ').norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have key := integral_mono i0 ((i1.const_mul (2 / s)).add (i2.const_mul (2 * s)))
    (fun t => pt _)
  simp only [Pi.add_apply] at key
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul] at key
  rw [b1, b2]
  exact key

theorem cube_sum {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : Set V) (u : V)
    (hu : u ∈ A) (s : ℝ) (hs : 0 < s) : ∀ (N : ℕ) (c : Fin N → ℝ → G) (D : Fin N → V → V),
    (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) →
    (∀ i, ∀ v ∈ A, D i v ∈ A) →
    ∃ (S : List V) (C : ℝ), (∀ v ∈ S, v ∈ A) ∧ 0 ≤ C ∧ ∀ Fr : V → G → ℂ, (∀ v ∈ A, Continuous (Fr v)) →
      (∀ v ∈ A, ∀ i x, HasDerivAt (fun t => Fr v (x * c i t)) (Fr (D i v) x) 0) →
      ‖Fr u 1‖ ^ 2 ≤ C * (S.map fun v => ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ‖Fr v (List.ofFn fun i => c i (t i)).prod‖ ^ 2).sum := by
  intro N
  induction N with
  | zero =>
    intro c D _ _
    refine ⟨[u], 1, by simpa using hu, zero_le_one, fun Fr _ _ => ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [volume_pi, Measure.restrict_pi_pi]
    simp [Measure.real]
  | succ N ih =>
    intro c D hc hD
    obtain ⟨S, C, hS, hC, h⟩ := ih (fun i => c i.castSucc) (fun i => D i.castSucc) (fun i => hc _)
      (fun i => hD _)
    refine ⟨S ++ S.map (D (Fin.last N)), C * (2 / s + 2 * s), ?_, by positivity, fun Fr h1 h2 => ?_⟩
    · intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hS v hv
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
        exact hD _ w (hS w hw)
    refine (h Fr h1 fun v hv i => h2 v hv _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    rw [List.map_append, List.sum_append, List.map_map, ← List.sum_map_add, ← List.sum_map_mul_left]
    refine List.sum_le_sum fun v hv => ?_
    refine (cube_step N c s hs hc (Fr v) (Fr (D (Fin.last N) v)) (h1 v (hS v hv))
      (h1 _ (hD _ v (hS v hv))) (h2 v (hS v hv) _)).trans ?_
    simp only [Function.comp_apply]
    have p : ∀ w, 0 ≤ ∫ t in Set.pi Set.univ (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s),
        ‖Fr w (List.ofFn fun i => c i (t i)).prod‖ ^ 2 := fun w => integral_nonneg fun t => by positivity
    have a1 := mul_nonneg (show 0 ≤ 2 * s by positivity) (p v)
    have a2 := mul_nonneg (show 0 ≤ 2 / s by positivity) (p (D (Fin.last N) v))
    nlinarith

theorem exists_small (n : ℕ) : ∃ s : ℝ, 0 < s ∧ n * (Real.exp (3 * n ^ 2 * s) - 1) ≤ 1 / 2 := by
  have h : ContinuousAt (fun s : ℝ => n * (Real.exp (3 * n ^ 2 * s) - 1)) 0 := by fun_prop
  have h2 : ∀ᶠ s : ℝ in 𝓝 0, n * (Real.exp (3 * n ^ 2 * s) - 1) < 1 / 2 :=
    h.eventually_lt continuousAt_const (by simp)
  obtain ⟨s, h3, h4⟩ := ((h2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨s, h4, h3.le⟩

theorem sobolev_at_one : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ F : List (Mx n) → Mx n → ℂ, (∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ContinuousOn (F l) (UJset ε)) → IsDerFam ε F → (∀ l ∈ S, Integrable (fun g : UJ ε => ‖F l (umat g)‖ ^ 2) (muG ε)) → ‖F [] 1‖ ^ 2 ≤ C * (S.map fun l => ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε)).sum := by
  intro n ε
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  obtain ⟨κ, hκ, hg, -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge n ε
  obtain ⟨s, hs, hsn⟩ := exists_small n
  let c : Fin (n ^ 2) → ℝ → UJ ε := fun i t =>
    GlobalTheory.GaugeConst.expJ ε (t • (⟨E i, (hE1 i).1⟩ : GlobalTheory.GaugeConst.lieJ ε))
  have hc : ∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b := fun i =>
    ⟨(GlobalTheory.GaugeConst.continuous_expJ ε).comp (continuous_id.smul continuous_const),
      GlobalTheory.GaugeConst.uMat_injective ε (by
        change NormedSpace.exp ((0 : ℝ) • E i) = 1
        simp),
      fun a b => GlobalTheory.GaugeConst.uMat_injective ε (exp_add_smul (E i) a b)⟩
  obtain ⟨S, C, hS, hC, h⟩ := cube_sum {l : List (Mx n) | ∀ Y ∈ l, Y ∈ lieSet ε} [] (by simp) s hs (n ^ 2) c
    (fun i l => E i :: l) hc (fun i l hl Y hY => by
      rcases List.mem_cons.1 hY with rfl | hY
      exacts [(hE1 i).1, hl Y hY])
  set K := Real.exp (2 * n ^ 3 * (Real.exp (2 * n ^ 2 * s) - 1)) * κ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨S, C * K, hS, by positivity, fun F hF hD hI => ?_⟩
  have hcont : ∀ l : List (Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → Continuous fun g : UJ ε => F l (umat g) :=
    fun l hl => (hF l hl).comp_continuous (GlobalTheory.GaugeConst.continuous_uMat ε) fun g => g.2
  refine (h (fun l g => F l (umat g)) hcont fun l hl i x => hD l hl (E i) (hE1 i).1 _ x.2).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun l hl => ?_
  have hl' := hcont l (hS l hl)
  have hΘ := continuous_prod_ofFn_curves (n ^ 2) c (fun i => (hc i).1)
  have hch := GlobalTheory.ProductChart.lintegral_chart_le n ε κ s E (fun t => (List.ofFn fun i => c i (t i)).prod) hg
    (fun i => (hE1 i).1) hE2 hs hsn (fun t => by
      have := map_list_prod ((Units.coeHom (Mx n)).comp (UJ ε).subtype) (List.ofFn fun i => c i (t i))
      refine this.trans ?_
      rw [List.map_ofFn]
      simp only [Complex.coe_smul]
      rfl)
    (fun g => ENNReal.ofReal (‖F l (umat g)‖ ^ 2)) (hl'.norm.pow 2).measurable.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t : Fin (n ^ 2) → ℝ => ‖F l (umat (List.ofFn fun i => c i (t i)).prod)‖ ^ 2)
    (Filter.Eventually.of_forall fun t => by positivity)
    ((hl'.comp hΘ).norm.pow 2).aestronglyMeasurable]
  have hp : 0 ≤ ∫ g : UJ ε, ‖F l (umat g)‖ ^ 2 ∂(muG ε) := integral_nonneg fun g => by positivity
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hp) (hch.trans ?_)
  rw [ENNReal.ofReal_mul hK0, ofReal_integral_eq_lintegral_ofReal (hI l hl)
    (Filter.Eventually.of_forall fun g => by positivity)]
  exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end GlobalTheory.SobolevHaar
