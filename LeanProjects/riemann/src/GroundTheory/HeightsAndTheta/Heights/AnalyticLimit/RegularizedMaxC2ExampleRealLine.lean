import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshRegMax
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)

noncomputable section

section C2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def TendstoC2On (F : ℝ → E → ℝ) (f : E → ℝ) (K : Set E) : Prop :=
  TendstoUniformlyOn F f (𝓝[>] 0) K ∧
    TendstoUniformlyOn (fun t y => fderiv ℝ (F t) y) (fderiv ℝ f) (𝓝[>] 0) K ∧
    TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ (F t)) y) (fderiv ℝ (fderiv ℝ f)) (𝓝[>] 0) K

def RegularizedMaxConvergenceC2.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] [Nonempty ι]
    (U K : Set E) (f : E → ℝ) (u : ℝ → ι → E → ℝ) (ε δ : ℝ → ℝ),
    IsOpen U → K ⊆ U → ContDiffOn ℝ 2 f U →
    (∀ᶠ t in 𝓝[>] 0, 0 < ε t ∧ ∀ j, ContDiffOn ℝ 2 (u t j) U) →
    Tendsto ε (𝓝[>] 0) (𝓝 0) →
    (∀ j, TendstoC2On (fun t => u t j) f K) →
    (∀ᶠ t in 𝓝[>] 0, ∀ j, ∀ x ∈ K, ‖fderiv ℝ (u t j) x - fderiv ℝ f x‖ ≤ δ t) →
    Tendsto (fun t => δ t ^ 2 / ε t) (𝓝[>] 0) (𝓝 0) →
    TendstoC2On (fun t x => regMax (ε t) (fun j => u t j x) + ε t / 2) f K

theorem norm_le_of_symm_diag {H : E →L[ℝ] E →L[ℝ] ℝ} (hs : ∀ v w, H v w = H w v) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ v, |H v v| ≤ c * ‖v‖ ^ 2) : ‖H‖ ≤ 2 * c := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun x y => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖y‖ := norm_pos_iff.2 hy
  set x' := ‖x‖⁻¹ • x
  set y' := ‖y‖⁻¹ • y
  have hx' : ‖x'‖ = 1 := by simp [x', norm_smul, ha.ne']
  have hy' : ‖y'‖ = 1 := by simp [y', norm_smul, hb.ne']
  have hxy : H x y = ‖x‖ * ‖y‖ * H x' y' := by
    simp only [x', y', map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  have key : 4 * H x' y' = H (x' + y') (x' + y') - H (x' - y') (x' - y') := by
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [hs y' x']
    ring
  have h1 : ‖x' + y'‖ ^ 2 ≤ 4 := by
    have := norm_add_le x' y'
    rw [hx', hy'] at this
    nlinarith [norm_nonneg (x' + y')]
  have h2 : ‖x' - y'‖ ^ 2 ≤ 4 := by
    have := norm_sub_le x' y'
    rw [hx', hy'] at this
    nlinarith [norm_nonneg (x' - y')]
  have k1 := hc (x' + y')
  have k2 := hc (x' - y')
  have s1 : c * ‖x' + y'‖ ^ 2 ≤ c * 4 := mul_le_mul_of_nonneg_left h1 hc0
  have s2 : c * ‖x' - y'‖ ^ 2 ≤ c * 4 := mul_le_mul_of_nonneg_left h2 hc0
  have hH : |H x' y'| ≤ 2 * c := by
    rw [abs_le] at k1 k2 ⊢
    constructor <;> linarith
  rw [Real.norm_eq_abs, hxy, abs_mul, abs_mul, abs_norm, abs_norm]
  have hab : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  calc ‖x‖ * ‖y‖ * |H x' y'| ≤ ‖x‖ * ‖y‖ * (2 * c) := mul_le_mul_of_nonneg_left hH hab
    _ = 2 * c * ‖x‖ * ‖y‖ := by ring

theorem fderiv2_sub_of_contDiffOn {U : Set E} (hU : IsOpen U) {φ ψ : E → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hψ : ContDiffOn ℝ 2 ψ U) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fderiv ℝ fun y => φ y - ψ y) x =
      fderiv ℝ (fderiv ℝ φ) x - fderiv ℝ (fderiv ℝ ψ) x := by
  have h : fderiv ℝ (fun y => φ y - ψ y) =ᶠ[𝓝 x] fun y => fderiv ℝ φ y - fderiv ℝ ψ y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_sub ((hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hψ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  rw [h.fderiv_eq]
  exact fderiv_sub
    (((hφ.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))
    (((hψ.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num))

theorem dist_lt_iff_norm_sub {F : Type*} [SeminormedAddCommGroup F] {a b : F} {e : ℝ} :
    dist a b < e ↔ ‖b - a‖ < e := by
  rw [dist_eq_norm, norm_sub_rev]

end C2

section RegMax

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem abs_fderiv_regMax_apply_le {η : ℝ} (hη : 0 < η) (p z : ι → ℝ) :
    |fderiv ℝ (regMax (ι := ι) η) p z| ≤ ‖z‖ := by
  classical
  set L := fderiv ℝ (regMax (ι := ι) η) p
  have hz : z = ∑ j, z j • Pi.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hLz : L z = ∑ j, z j * L (Pi.single j 1) := by
    conv_lhs => rw [hz]
    simp [map_sum, map_smul]
  have hs : ∑ j, L (Pi.single j 1) = 1 := regMax_fderiv_sum hη p
  have hn : ∀ j, 0 ≤ L (Pi.single j 1) := fun j =>
    regMax_fderiv_nonneg hη p _ (Pi.single_nonneg.2 zero_le_one)
  rw [hLz]
  calc |∑ j, z j * L (Pi.single j 1)| ≤ ∑ j, |z j * L (Pi.single j 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |z j| * L (Pi.single j 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hn j)]
    _ ≤ ∑ j, ‖z‖ * L (Pi.single j 1) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (hn j)
        simpa [Real.norm_eq_abs] using norm_le_pi_norm z j
    _ = ‖z‖ := by rw [← Finset.mul_sum, hs, mul_one]

theorem norm_fderiv2_regMax_le : ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ p : ι → ℝ,
    ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p‖ ≤ C / η := by
  obtain ⟨C, hC⟩ := regMax_one_fderiv2_bound (ι := ι)
  refine ⟨C, fun η hη p => ?_⟩
  rw [fderiv2_regMax hη]
  calc ‖η⁻¹ • fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖
      ≤ ‖η⁻¹‖ * ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖ :=
        ContinuousLinearMap.opNorm_smul_le η⁻¹ (fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p))
    _ = η⁻¹ * ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • p)‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
    _ ≤ η⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) (inv_pos.2 hη).le
    _ = C / η := by ring

end RegMax

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem norm_le_sum_norm {F : Type*} [NormedAddCommGroup F] (a : ι → F) (j : ι) :
    ‖a j‖ ≤ ∑ i, ‖a i‖ :=
  Finset.single_le_sum (f := fun i => ‖a i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)

omit [Nonempty ι] in
theorem abs_le_sum_abs (a : ι → ℝ) (j : ι) : |a j| ≤ ∑ i, |a i| :=
  Finset.single_le_sum (f := fun i => |a i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem regMax_c2_pointwise_bound {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {η : ℝ} (hη : 0 < η) {C : ℝ}
    (hC : ∀ p : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p‖ ≤ C / η) {z : E} (hz : z ∈ U)
    {s0 s1 s2 : ℝ} (h0 : ∀ j, |u j z - f z| ≤ s0)
    (h1 : ∀ j, ‖fderiv ℝ (u j) z - fderiv ℝ f z‖ ≤ s1)
    (h2 : ∀ j, ‖fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z‖ ≤ s2) :
    |(regMax η (fun j => u j z) + η / 2) - f z| ≤ s0 + η ∧
      ‖fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) z - fderiv ℝ f z‖ ≤ s1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2)) z -
          fderiv ℝ (fderiv ℝ f) z‖ ≤ 2 * (C / η * s1 ^ 2 + s2) := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  have hs0 : 0 ≤ s0 := (h0 j₀).trans' (abs_nonneg _)
  have hs1 : 0 ≤ s1 := (h1 j₀).trans' (norm_nonneg _)
  have hs2 : 0 ≤ s2 := (h2 j₀).trans'
    (norm_nonneg (fderiv ℝ (fderiv ℝ (u j₀)) z - fderiv ℝ (fderiv ℝ f) z))
  have hCη : 0 ≤ C / η :=
    (hC 0).trans' (norm_nonneg (fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) 0))
  have hdiff : ∀ {φ : E → ℝ}, ContDiffOn ℝ 2 φ U → ∀ y ∈ U, DifferentiableAt ℝ φ y :=
    fun hφ y hy => (hφ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hdiff2 : ∀ {φ : E → ℝ}, ContDiffOn ℝ 2 φ U → DifferentiableAt ℝ (fderiv ℝ φ) z :=
    fun hφ => ((hφ.contDiffAt (hU.mem_nhds hz)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  let b : ι → E → ℝ := fun j x => u j x - f x
  have hb : ∀ j, ContDiffOn ℝ 2 (b j) U := fun j => (hu j).sub hf
  have hbv : ContDiffOn ℝ 2 (fun x j => b j x) U := contDiffOn_pi.2 hb
  let g : E → ℝ := fun x => regMax η (fun j => b j x)
  have hg2 : ContDiffOn ℝ 2 g U :=
    ((regMax_contDiff (ι := ι) hη).of_le two_le_inf).comp_contDiffOn hbv
  have hval : ∀ x, regMax η (fun j => u j x) = g x + f x := by
    intro x
    have := regMax_add_const η (fun j => b j x) (f x)
    simpa [b, g] using this
  have hG : (fun x => regMax η (fun j => u j x) + η / 2) = fun x => g x + f x + η / 2 := by
    funext x
    rw [hval]
  have hDG : ∀ y ∈ U, fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) y =
      fderiv ℝ g y + fderiv ℝ f y := by
    intro y hy
    rw [hG, fderiv_add_const]
    exact fderiv_add (hdiff hg2 y hy) (hdiff hf y hy)
  have hDb : ∀ j, fderiv ℝ (b j) z = fderiv ℝ (u j) z - fderiv ℝ f z := fun j =>
    fderiv_sub (hdiff (hu j) z hz) (hdiff hf z hz)
  have hgz : HasFDerivAt g ((fderiv ℝ (regMax (ι := ι) η) (fun j => b j z)).comp
      (ContinuousLinearMap.pi fun j => fderiv ℝ (b j) z)) z := by
    have hbz : HasFDerivAt (fun x j => b j x) (ContinuousLinearMap.pi fun j => fderiv ℝ (b j) z) z :=
      hasFDerivAt_pi.2 fun j => (hdiff (hb j) z hz).hasFDerivAt
    exact ((regMax_contDiff (ι := ι) hη).differentiable (by simp) _).hasFDerivAt.comp z hbz
  have hnb1 : ∀ v, ‖(fun j => fderiv ℝ (b j) z v)‖ ≤ s1 * ‖v‖ := by
    intro v
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [hDb]
    exact ((fderiv ℝ (u j) z - fderiv ℝ f z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h1 j) (norm_nonneg v))
  refine ⟨?_, ?_, ?_⟩
  · rw [hval]
    have hm := abs_regMax_le hη.le (fun j => b j z)
    have hbn : ‖(fun j => b j z)‖ ≤ s0 :=
      (pi_norm_le_iff_of_nonneg hs0).2 fun j => by rw [Real.norm_eq_abs]; exact h0 j
    have e : g z + f z + η / 2 - f z = g z + η / 2 := by ring
    rw [e]
    calc |g z + η / 2| ≤ |g z| + |η / 2| := abs_add_le _ _
      _ ≤ s0 + η := by
        rw [abs_of_pos (by positivity : (0 : ℝ) < η / 2)]
        have : |g z| ≤ ‖(fun j => b j z)‖ + η / 2 := hm
        linarith
  · rw [hDG z hz, add_sub_cancel_right, hgz.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ hs1 fun v => ?_
    rw [ContinuousLinearMap.comp_apply, Real.norm_eq_abs]
    exact (abs_fderiv_regMax_apply_le hη _ _).trans (hnb1 v)
  · have hD2G : fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2)) z =
        fderiv ℝ (fderiv ℝ g) z + fderiv ℝ (fderiv ℝ f) z := by
      have h : fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) =ᶠ[𝓝 z]
          fun y => fderiv ℝ g y + fderiv ℝ f y :=
        Filter.eventually_of_mem (hU.mem_nhds hz) hDG
      rw [h.fderiv_eq]
      exact fderiv_add (hdiff2 hg2) (hdiff2 hf)
    rw [hD2G, add_sub_cancel_right]
    have hsym : ∀ v w, fderiv ℝ (fderiv ℝ g) z v w = fderiv ℝ (fderiv ℝ g) z w v :=
      (hg2.contDiffAt (hU.mem_nhds hz)).isSymmSndFDerivAt (by simp)
    refine norm_le_of_symm_diag hsym (by positivity) fun v => ?_
    have key : fderiv ℝ (fderiv ℝ g) z v v =
        fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z) (fun j => fderiv ℝ (b j) z v)
            (fun j => fderiv ℝ (b j) z v) +
          fderiv ℝ (regMax (ι := ι) η) (fun j => b j z)
            (fun j => fderiv ℝ (fderiv ℝ (b j)) z v v) :=
      regMax_comp_fderiv2 hη hU hb hz v
    rw [key]
    have hr : ‖(fun j => fderiv ℝ (fderiv ℝ (b j)) z v v)‖ ≤ s2 * ‖v‖ ^ 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have e : fderiv ℝ (fderiv ℝ (b j)) z =
          fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z :=
        fderiv2_sub_of_contDiffOn hU (hu j) hf hz
      rw [e]
      calc ‖(fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z) v v‖
          ≤ ‖fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z‖ * ‖v‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm₂ _ v v
        _ ≤ s2 * ‖v‖ * ‖v‖ := by gcongr; exact h2 j
        _ = s2 * ‖v‖ ^ 2 := by ring
    have hm1 := abs_fderiv_regMax_apply_le hη (fun j => b j z)
      (fun j => fderiv ℝ (fderiv ℝ (b j)) z v v)
    have hm2 : |fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z)
        (fun j => fderiv ℝ (b j) z v) (fun j => fderiv ℝ (b j) z v)| ≤ C / η * (s1 * ‖v‖) ^ 2 := by
      rw [← Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => b j z)‖ *
            ‖(fun j => fderiv ℝ (b j) z v)‖ * ‖(fun j => fderiv ℝ (b j) z v)‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ C / η * (s1 * ‖v‖) * (s1 * ‖v‖) := by
            gcongr
            · exact hC _
            · exact hnb1 v
            · exact hnb1 v
        _ = C / η * (s1 * ‖v‖) ^ 2 := by ring
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ C / η * (s1 * ‖v‖) ^ 2 + s2 * ‖v‖ ^ 2 := add_le_add hm2 (hm1.trans hr)
      _ = (C / η * s1 ^ 2 + s2) * ‖v‖ ^ 2 := by ring

end Main

theorem RegularizedMaxConvergenceC2.proof : RegularizedMaxConvergenceC2.Statement := by
  intro E _ _ ι _ _ U K f u ε δ hU hK hf hev hε hc hδ hδε
  obtain ⟨C, hC⟩ := norm_fderiv2_regMax_le (ι := ι)
  have hC0 : 0 ≤ C := by
    simpa using (hC 1 one_pos 0).trans' (norm_nonneg (fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) 0))
  have hc0 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K, |u t j x - f x| < e := fun j e he =>
    (Metric.tendstoUniformlyOn_iff.1 (hc j).1 e he).mono fun t ht x hx => by
      simpa [Real.dist_eq, abs_sub_comm] using ht x hx
  have hc1 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K,
      ‖fderiv ℝ (u t j) x - fderiv ℝ f x‖ < e := fun j e he =>
    (Metric.tendstoUniformlyOn_iff.1 (hc j).2.1 e he).mono fun t ht x hx => by
      simpa [dist_eq_norm, norm_sub_rev] using ht x hx
  have hc2 : ∀ j, ∀ e > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ K,
      ‖fderiv ℝ (fderiv ℝ (u t j)) x - fderiv ℝ (fderiv ℝ f) x‖ < e := fun j e he =>
    ((Metric.tendstoUniformlyOn_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).1 (hc j).2.2 e he).mono
      fun t ht x hx => (dist_lt_iff_norm_sub (F := E →L[ℝ] E →L[ℝ] ℝ)).1 (ht x hx)
  refine ⟨Metric.tendstoUniformlyOn_iff.2 fun e he => ?_,
    Metric.tendstoUniformlyOn_iff.2 fun e he => ?_,
    (Metric.tendstoUniformlyOn_iff (α := E →L[ℝ] E →L[ℝ] ℝ)).2 fun e he => ?_⟩
  · filter_upwards [hev, eventually_all.2 fun j => hc0 j (e / 3) (by positivity),
      hε.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < e / 3))] with t ht h0 hεe
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => (h0 j x hx).le) (fun j => norm_le_sum_norm (fun i => fderiv ℝ (u t i) x - fderiv ℝ f x) j)
      (fun j => norm_le_sum_norm
        (fun i => fderiv ℝ (fderiv ℝ (u t i)) x - fderiv ℝ (fderiv ℝ f) x) j)
    rw [Real.dist_eq, abs_sub_comm]
    linarith [P.1]
  · filter_upwards [hev, eventually_all.2 fun j => hc1 j (e / 2) (by positivity)] with t ht h1
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => abs_le_sum_abs (fun i => u t i x - f x) j) (fun j => (h1 j x hx).le)
      (fun j => norm_le_sum_norm
        (fun i => fderiv ℝ (fderiv ℝ (u t i)) x - fderiv ℝ (fderiv ℝ f) x) j)
    rw [dist_eq_norm, norm_sub_rev]
    linarith [P.2.1]
  · filter_upwards [hev, hδ, eventually_all.2 fun j => hc2 j (e / 8) (by positivity),
      hδε.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < e / (8 * (C + 1))))]
      with t ht hδt h2 hr
    intro x hx
    have P := regMax_c2_pointwise_bound hU hf ht.2 ht.1 (hC _ ht.1) (hK hx)
      (fun j => abs_le_sum_abs (fun i => u t i x - f x) j) (fun j => hδt j x hx)
      (fun j => (h2 j x hx).le)
    refine (dist_lt_iff_norm_sub (F := E →L[ℝ] E →L[ℝ] ℝ)).2 ?_
    have hq0 : 0 ≤ δ t ^ 2 / ε t := div_nonneg (sq_nonneg _) ht.1.le
    have hq : C * (δ t ^ 2 / ε t) < e / 8 := by
      calc C * (δ t ^ 2 / ε t) ≤ (C + 1) * (δ t ^ 2 / ε t) := by nlinarith
        _ < (C + 1) * (e / (8 * (C + 1))) := mul_lt_mul_of_pos_left hr (by linarith)
        _ = e / 8 := by field_simp
    have e1 : C / ε t * δ t ^ 2 = C * (δ t ^ 2 / ε t) := by ring
    have := P.2.2
    rw [e1] at this
    linarith

section System

open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}

theorem System.tendstoC2On_chart_symm_compact (S : System R) (k : Fin A.n) {K : Set (Fin D → ℂ)} (hK : IsCompact K)
    (hKs : K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo) :
    TendstoC2On (fun t y => S.ph t ((A.chart k).symm y)) (fun y => R.φ ((A.chart k).symm y)) K :=
  S.c2 k K hK hKs

end System

theorem regularizedMax_c2_example_real_line :
    TendstoC2On (fun t x => regMax t (fun j : Fin 2 => x ^ 2 + ((j : ℕ) : ℝ) * t) + t / 2)
      (fun x : ℝ => x ^ 2) (Set.Icc (-1) 1) := by
  have hd1 : ∀ c : ℝ, fderiv ℝ (fun x : ℝ => x ^ 2 + c) = fderiv ℝ (fun x : ℝ => x ^ 2) :=
    fun c => funext fun y => fderiv_add_const c
  refine RegularizedMaxConvergenceC2.proof (Fin 2) Set.univ (Set.Icc (-1) 1) (fun x : ℝ => x ^ 2)
    (fun t j x => x ^ 2 + ((j : ℕ) : ℝ) * t) (fun t => t) (fun _ => 0) isOpen_univ
    (Set.subset_univ _) (by fun_prop) ?_ ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact ⟨ht, fun j => by fun_prop⟩
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · intro j
    refine ⟨Metric.tendstoUniformlyOn_iff.2 fun e he => ?_, ?_, ?_⟩
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds he)]
        with t (ht : 0 < t) hte
      intro x _
      have hj : ((j : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Real.dist_eq, abs_sub_comm, add_sub_cancel_left, abs_of_nonneg (by positivity)]
      nlinarith
    · simp only [hd1]
      exact tendstoUniformlyOn_self _ _ _
    · simp only [hd1]
      exact tendstoUniformlyOn_self _ _ _
  · exact Eventually.of_forall fun t j x _ => by simp
  · simp

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
