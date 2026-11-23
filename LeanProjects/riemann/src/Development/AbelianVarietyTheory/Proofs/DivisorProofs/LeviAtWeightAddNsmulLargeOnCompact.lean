import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LeviLarge

theorem contDiffAt_ph {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) :
    ContDiffAt ℝ 2 (A.ph la i ∘ (A.chart i).symm) (A.chart i y) :=
  ((A.smooth_ph la i).contDiffAt
    ((A.chart i).open_target.mem_nhds ((A.chart i).map_source hy))).of_le (WithTop.coe_le_coe.2 le_top)

theorem leviAt_ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G H : La) (i : ι) {y : Y} (hy : y ∈ (A.chart i).source)
    (ξ : Fin n → ℂ) : ∀ k : ℕ,
    A.leviAt i (A.ph (G + k • H) i) y ξ = A.leviAt i (A.ph G i) y ξ + k * A.leviAt i (A.ph H i) y ξ
  | 0 => by simp
  | k + 1 => by
    have e : A.ph (G + (k + 1) • H) i =ᶠ[𝓝 y] fun x => A.ph (G + k • H) i x + A.ph H i x := by
      filter_upwards [(A.chart i).open_source.mem_nhds hy] with x hx
      rw [succ_nsmul, ← add_assoc, A.ph_add _ _ i x hx]
    rw [leviAt_congr A i _ _ y hy e ξ,
      leviAt_add A i _ _ y (contDiffAt_ph A _ i hy) (contDiffAt_ph A _ i hy) ξ,
      leviAt_ph_nsmul A G H i hy ξ k]
    push_cast; ring

theorem re_leviV_lower {n : ℕ} (g : V n → ℂ) (u : V n) (B : ℝ)
    (hFu : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ ≤ B) (ξ : Fin n → ℂ) :
    -(2 * B) * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n g u ξ).re := by
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : ∀ j k, ‖ξ j‖ * ‖ξ k‖ ≤ 2 * ∑ j, ‖ξ j‖ ^ 2 := by
    intro j k
    have h1 : ‖ξ j‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : ‖ξ k‖ ^ 2 ≤ ∑ j, ‖ξ j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖ξ j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    nlinarith [sq_nonneg (‖ξ j‖ - ‖ξ k‖), norm_nonneg (ξ j), norm_nonneg (ξ k)]
  have hnorm : ‖leviV n g u ξ‖ ≤ ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    unfold leviV
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hS j k) (norm_nonneg _)
  have h3 : ∑ j, ∑ k, ‖wd n j (wdb n k g) u‖ * (2 * ∑ j, ‖ξ j‖ ^ 2) =
      (∑ j, ∑ k, ‖wd n j (wdb n k g) u‖) * (2 * ∑ j, ‖ξ j‖ ^ 2) := by
    rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]
  have h4 := Complex.abs_re_le_norm (leviV n g u ξ)
  have h5 := neg_abs_le (leviV n g u ξ).re
  have h6 := mul_le_mul_of_nonneg_right hFu (by positivity : (0:ℝ) ≤ 2 * ∑ j, ‖ξ j‖ ^ 2)
  linarith

theorem curv_large : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (i : ι) (K : Set (V n)) (t : ℝ), IsCompact K → K ⊆ (A.chart i).target → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ v ∈ K, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt i (A.ph (G + k • H) i) ((A.chart i).symm v) ξ := by
  intro n Y _ _ _ _ _ ι La _ A H G hH i K t hK hKU
  have hU : IsOpen (A.chart i).target := (A.chart i).open_target
  have hsm : ∀ la : La, ContDiffOn ℝ ∞ (fun v => ((A.ph la i ((A.chart i).symm v) : ℝ) : ℂ))
      (A.chart i).target :=
    fun la => Complex.ofRealCLM.contDiff.comp_contDiffOn (A.smooth_ph la i)
  obtain ⟨c, hc, hcK⟩ := levi_pos_compact hU (hsm H) hK hKU (fun u hu ζ hζ => by
    have hyu := (A.chart i).map_target (hKU hu)
    have hne : ζ.ofLp ≠ 0 := by simpa using hζ
    have := hH i _ hyu ζ.ofLp hne
    simpa [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hu)] using this)
  have hF : ContinuousOn (fun u => ∑ j, ∑ k,
      ‖wd n j (wdb n k (fun v => ((A.ph G i ((A.chart i).symm v) : ℝ) : ℂ))) u‖) K :=
    continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
      ((continuousOn_wd_wdb hU (hsm G) j k).mono hKU).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨⌈(t + 2 * B) / c⌉₊, fun k hk v hv ξ => ?_⟩
  have hy := (A.chart i).map_target (hKU hv)
  rw [leviAt_ph_nsmul A G H i hy ξ k]
  simp only [WeightedAtlas.leviAt, (A.chart i).right_inv (hKU hv)]
  have hFu := (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hB v hv)
  have hG := re_leviV_lower _ v B hFu ξ
  have hc' := hcK v hv (WithLp.toLp 2 ξ)
  rw [EuclideanSpace.norm_sq_eq] at hc'
  simp only [PiLp.toLp_apply, WithLp.ofLp_toLp] at hc'
  have hk' : (t + 2 * B) / c ≤ k := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hkc : t + 2 * B ≤ k * c := by rwa [div_le_iff₀ hc] at hk'
  have hS0 : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg (α := ℝ) k)
  have h2 := mul_le_mul_of_nonneg_right hkc hS0
  nlinarith

end GlobalTheory.OTY.LeviLarge
