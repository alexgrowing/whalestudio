import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow

noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Unfold

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
  {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem lintegral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫⁻ x, f x ∂μ := by
  rw [h.lintegral_eq_tsum'' f, lintegral_tsum (f := fun (γ : Γ) x => f (γ * x)) fun γ : Γ =>
    (hf.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict]
  rfl

theorem integral_tsum_eq (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hf : Integrable f μ) :
    IntegrableOn (fun x => ∑' γ : Γ, f (γ * x)) 𝓕 μ ∧ ∫ x in 𝓕, ∑' γ : Γ, f (γ * x) ∂μ = ∫ x, f x ∂μ := by
  have hm : ∀ γ : Γ, AEStronglyMeasurable (fun x => f (γ * x)) (μ.restrict 𝓕) := fun γ =>
    (hf.1.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving).restrict
  have hl : ∑' γ : Γ, ∫⁻ x in 𝓕, ‖f (γ * x)‖ₑ ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    rw [← lintegral_tsum fun γ => (hm γ).enorm, lintegral_tsum_eq h hf.1.enorm]
  refine ⟨⟨AEStronglyMeasurable.tsum hm, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun γ => (hm γ).enorm, hl]
    exact hf.2
  · rw [integral_tsum hm (hl ▸ hf.2.ne), h.integral_eq_tsum'' f hf]
    rfl

end Unfold

section Dbl

variable {G G₂ : Type} [Group G] [Group G₂] (i : G × G →* G₂) {P Γ₂ : Subgroup G₂} {Γ : Subgroup G} {r : Γ → Γ₂}

theorem cosetSum_io {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (h x : G) :
    cosetSum P Γ₂ Φ (i (h, x)) = ∑' δ : Γ, Φ (i (h, δ * x)) ∧
      (CosetConv P Γ₂ Φ (i (h, x)) ↔ Summable fun δ : Γ => ‖Φ (i (h, δ * x))‖) := by
  have e : ∀ δ : Γ, (r δ : G₂) * i (h, x) = i (h, δ * x) := fun δ => by
    rw [hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  refine ⟨(cosetSum_eq_tsum hΦ hr _).trans (tsum_congr fun δ => by rw [e]), ?_⟩
  rw [cosetConv_iff hΦ hr]
  exact summable_congr fun δ => by rw [e]

variable [MeasurableSpace G] [MeasurableMul G] [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G}

theorem unfold_core (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ)
    (hri : ∀ δ, (r δ : G₂) = i (1, δ)) (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ))
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hw : ∀ x y, w (x * y) = w x * w y)
    (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (hwm : AEStronglyMeasurable w μ)
    (hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ) (h : G)
    (hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  set F : G → ℂ := fun x => Φ (i (h, x)) * w x with hF
  have hFm : AEStronglyMeasurable F μ := (hm h).mul hwm
  have hFn : ∀ x, ‖F x‖ₑ = ‖Φ (i (h, x))‖ₑ := fun x => by
    rw [hF, enorm_mul, ← ofReal_norm_eq_enorm (w x), hw1, ENNReal.ofReal_one, mul_one]
  have hFi : Integrable F μ := by
    refine ⟨hFm, ?_⟩
    rw [HasFiniteIntegral, lintegral_congr (fun x => hFn x), ← lintegral_tsum_eq h𝓕 (hm h).enorm]
    exact lt_top_iff_ne_top.2 hfin
  have hδ : ∀ x, ∑' δ : Γ, F (δ * x) = cosetSum P Γ₂ Φ (i (h, x)) * w x := fun x => by
    rw [(cosetSum_io i hΦ hri hr h x).1, ← tsum_mul_right]
    exact tsum_congr fun δ => by
      show Φ _ * w (δ * x) = _
      rw [hw, hwΓ _ δ.2, one_mul]
  have hsh : ∀ x, F (h * x) = c h * w h * (Φ (i (1, x)) * w x) := fun x => by
    have : i (h, h * x) = i (h, h) * i (1, x) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [hF]; simp only [this, hlaw, hw]; ring
  have hsh' : ∀ x, Φ (i (1, x)) * w x = c h⁻¹ * w h⁻¹ * F (h * x) := fun x => by
    have : i (1, x) = i (h⁻¹, h⁻¹) * i (h, h * x) := by
      rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel_left]
    have hx : w x = w h⁻¹ * w (h * x) := by rw [← hw, inv_mul_cancel_left]
    rw [hF]; simp only [this, hlaw, hx]; ring
  have hFh : Integrable (fun x => F (h * x)) μ := hFi.comp_mul_left h
  obtain ⟨h1, h2⟩ := integral_tsum_eq h𝓕 hFi
  refine ⟨(hFh.const_mul (c h⁻¹ * w h⁻¹)).congr (Eventually.of_forall fun x => (hsh' x).symm), ?_, ?_⟩
  · exact Integrable.congr h1 (Eventually.of_forall hδ)
  · rw [← setIntegral_congr_fun₀ ?_ (fun x _ => hδ x), h2, ← integral_mul_left_eq_self F h]
    · simp only [hsh]; rw [integral_const_mul]
    · exact h𝓕.nullMeasurableSet

end Dbl

section Passage

variable {s₀ : ℂ}

theorem holValueAt_sum {ι : Type} (T : Finset ι) {f : ι → ℂ → ℂ} {z : ι → ℂ}
    (h : ∀ j ∈ T, HolValueAt (f j) s₀ (z j)) : HolValueAt (fun s => ∑ j ∈ T, f j s) s₀ (∑ j ∈ T, z j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem holValueAt_integral_of_expansion {X ι : Type} [MeasurableSpace X] {ν : Measure X} [Fintype ι]
    {Φ : ℂ → X → ℂ} {Ψ : X → ℂ} {c : ι → X → ℂ} {v : ι → ℂ → ℂ} {w : ι → ℂ} {σ : ℝ}
    (hc : ∀ j, Integrable (c j) ν) (hexp : ∀ s : ℂ, σ < s.re → ∀ x, Φ s x = ∑ j, c j x * v j s)
    (hv : ∀ j, HolValueAt (v j) s₀ (w j)) (hΨ : ∀ x, HolValueAt (fun s => Φ s x) s₀ (Ψ x)) :
    (∀ x, Ψ x = ∑ j, c j x * w j) ∧ Integrable Ψ ν ∧ HolValueAt (fun s => ∫ x, Φ s x ∂ν) s₀ (∫ x, Ψ x ∂ν) := by
  have hΨe : ∀ x, Ψ x = ∑ j, c j x * w j := fun x =>
    (hΨ x).unique ((holValueAt_sum Finset.univ fun j _ => (holValueAt_const (c j x) s₀).mul (hv j)).congr
      ⟨σ, fun s hs => (hexp s hs x).symm⟩)
  have hΨi : Integrable Ψ ν := by
    rw [funext hΨe]
    exact integrable_finset_sum _ fun j _ => (hc j).mul_const (w j)
  refine ⟨hΨe, hΨi, ?_⟩
  have e1 : ∫ x, Ψ x ∂ν = ∑ j, (∫ x, c j x ∂ν) * w j := by
    rw [funext hΨe, integral_finset_sum _ fun j _ => (hc j).mul_const (w j)]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  rw [e1]
  refine (holValueAt_sum Finset.univ fun j _ => (holValueAt_const (∫ x, c j x ∂ν) s₀).mul (hv j)).congr
    ⟨σ, fun s hs => ?_⟩
  simp only
  rw [integral_congr_ae (Eventually.of_forall (hexp s hs)),
    integral_finset_sum _ fun j _ => (hc j).mul_const (v j s)]
  exact Finset.sum_congr rfl fun j _ => (integral_mul_const _ _).symm

end Passage

section Expansion

variable {G₂ : Type} [Group G₂] {P Γ₂ K : Subgroup G₂} {ι : Type} [Fintype ι] {kk : ι → G₂} {c : ι → G₂ → ℂ}

theorem flatSec_expansion {δ : P →* ℝ≥0} (hI : IsIwasawa δ K) {f : G₂ → ℂ} (hkk : ∀ j, kk j ∈ K)
    (hexp : ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j)) (s₀ s : ℂ) (g : G₂) {k : G₂} (hk : k ∈ K) :
    flatSec δ K f s₀ s (g * k) = ∑ j, c j k * flatSec δ K f s₀ s (g * kk j) := by
  simp only [flatSec, hI.iwAbs_right g hk, hI.iwAbs_right g (hkk _), hexp g k hk, Finset.sum_mul, mul_assoc]

theorem cosetSum_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j)) (y : G₂)
    (hconv : ∀ j, CosetConv P Γ₂ Φ (y * kk j)) {k : G₂} (hk : k ∈ K) :
    cosetSum P Γ₂ Φ (y * k) = ∑ j, c j k * cosetSum P Γ₂ Φ (y * kk j) := by
  have e : ∀ q, term P Γ₂ Φ (y * k) q = ∑ j, c j k * term P Γ₂ Φ (y * kk j) q := fun q => by
    simp only [term, ← mul_assoc]
    exact hexp _ k hk
  rw [cosetSum, tsum_congr e, Summable.tsum_finsetSum fun j _ => ((hconv j).of_norm).mul_left (c j k)]
  exact Finset.sum_congr rfl fun j _ => tsum_mul_left

theorem cosetSum_norm_expansion {Φ : G₂ → ℂ} (hexp : ∀ g, ∀ k ∈ K, Φ (g * k) = ∑ j, c j k * Φ (g * kk j))
    (y : G₂) {k : G₂} (hk : k ∈ K) :
    ∑' q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ∑' q, ‖term P Γ₂ Φ (y * kk j) q‖ₑ := by
  have e : ∀ q, ‖term P Γ₂ Φ (y * k) q‖ₑ ≤ ∑ j, ‖c j k‖ₑ * ‖term P Γ₂ Φ (y * kk j) q‖ₑ := fun q => by
    simp only [term, ← mul_assoc]
    rw [hexp _ k hk]
    refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (enorm_mul _ _).le)
  refine (ENNReal.tsum_le_tsum e).trans ?_
  rw [Summable.tsum_finsetSum fun j _ => ENNReal.summable]
  exact le_of_eq (Finset.sum_congr rfl fun j _ => ENNReal.tsum_mul_left)

end Expansion

section Cover

theorem measure_le_of_cover {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {C : Set G}
    (hcov : ∀ x, ∃ γ : Γ, (γ : G) * x ∈ C) : μ 𝓕 ≤ μ C := by
  rw [h𝓕.measure_eq_tsum C]
  refine le_trans (measure_mono fun x hx => ?_) (measure_iUnion_le _)
  obtain ⟨γ, hγ⟩ := hcov x
  exact mem_iUnion.2 ⟨γ⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by simpa [Subgroup.smul_def] using hγ), hx⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ K : Subgroup G} [Countable Γ]

theorem measure_lt_top_of_cover {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) : μ 𝓕 < ⊤ := by
  refine lt_of_le_of_lt (measure_le_of_cover h𝓕 (C := ⋃ a ∈ A, (a * ·) '' (K : Set G)) fun x => ?_)
    ((A.isCompact_biUnion fun a _ => hKc.image (continuous_mul_left a)).measure_lt_top)
  obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
  exact ⟨⟨γ⁻¹, inv_mem hγ⟩, mem_biUnion ha ⟨k, hk, by simp [mul_assoc]⟩⟩

open Classical in

theorem exists_coeff (hK : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (A : Finset G)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) {ι : Type} [Fintype ι] (c : ι → G → ℂ)
    (hc : ∀ j, Continuous (c j)) :
    ∃ C : G → ι → G → ℂ, (∀ a j, Measurable (C a j)) ∧ (∃ M : ℝ, ∀ a j x, ‖C a j x‖ ≤ M) ∧
      ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k ∧ ∀ a' j, C a' j x = if a' = a then c j k else 0 := by
  classical
  haveI : Nonempty (Γ × A) := by
    obtain ⟨a, ha, γ, hγ, -⟩ := hcov 1
    exact ⟨(⟨γ, hγ⟩, ⟨a, ha⟩)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Γ × A)
  set y : ℕ → G → G := fun n x => ((e n).2 : G)⁻¹ * ((e n).1 : G)⁻¹ * x with hy
  have hyc : ∀ n, Continuous (y n) := fun n => continuous_const.mul continuous_id
  have hex : ∀ x, ∃ n, y n x ∈ K := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl⟩ := hcov x
    obtain ⟨n, hn⟩ := he (⟨γ, hγ⟩, ⟨a, ha⟩)
    exact ⟨n, by simpa [hy, hn, mul_assoc] using hk⟩
  have hM : ∀ j, ∃ M, ∀ x ∈ K, ‖c j x‖ ≤ M := fun j => hKc.exists_bound_of_continuousOn (hc j).continuousOn
  choose M hM using hM
  refine ⟨fun a' j x => if a' = ((e (Nat.find (hex x))).2 : G) then c j (y (Nat.find (hex x)) x) else 0,
    fun a' j => ?_, ⟨∑ j, |M j|, fun a' j x => ?_⟩, fun x => ?_⟩
  · refine Measurable.find (f := fun n x => if a' = ((e n).2 : G) then c j (y n x) else 0)
      (p := fun n x => y n x ∈ K) (fun n => ?_) (fun n => (hK.preimage (hyc n)).measurableSet) hex
    by_cases h : a' = ((e n).2 : G)
    · simp only [h, ite_true]; exact ((hc j).comp (hyc n)).measurable
    · simpa [h] using measurable_const
  · dsimp only
    split_ifs
    · exact (hM j _ (Nat.find_spec (hex x))).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
    · rw [norm_zero]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
  · refine ⟨((e (Nat.find (hex x))).2 : G), (e (Nat.find (hex x))).2.2, ((e (Nat.find (hex x))).1 : G),
      (e (Nat.find (hex x))).1.2, y (Nat.find (hex x)) x, Nat.find_spec (hex x), by simp [hy, mul_assoc], fun a' j => rfl⟩

end Cover

end GlobalTheory.DefDoubling
