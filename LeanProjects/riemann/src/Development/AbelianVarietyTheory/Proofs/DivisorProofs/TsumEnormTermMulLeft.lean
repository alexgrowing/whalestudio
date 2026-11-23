import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolValueAtIntegralOfExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateEqSumOfIsKFinite

noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Main

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {ι : Type} [Fintype ι] {kk : ι → G₂} {cc : ι → G₂ → ℂ}

theorem tsum_enorm_term_mul_left {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) {γ : G₂} (hγ : γ ∈ Γ₂) (g : G₂) :
    ∑' q, ‖term P Γ₂ Φ (γ * g) q‖ₑ = ∑' q, ‖term P Γ₂ Φ g q‖ₑ :=
  (tsum_congr fun q => by rw [term_mul_left hΦ ⟨γ, hγ⟩ g q]).trans ((rmulEquiv P Γ₂ ⟨γ, hγ⟩).tsum_eq fun q => ‖term P Γ₂ Φ g q‖ₑ)

theorem unfold (hi : Continuous i) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hΦc : Continuous Φ) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ g, ∀ k ∈ K₂, Φ (g * k) = ∑ j, cc j k * Φ (g * kk j)) (hconv : ∀ g, CosetConv P Γ₂ Φ g)
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hwc : Continuous w)
    (hw : ∀ x y, w (x * y) = w x * w y) (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (h : G) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  have hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ := fun h =>
    (hΦc.comp (hi.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  obtain ⟨C, -, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))

  set S : G₂ → ℝ≥0∞ := fun g => ∑' q, ‖term P Γ₂ Φ g q‖ₑ with hS
  have hSfin : ∀ g, S g ≠ ⊤ := fun g => by
    have := ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg (term P Γ₂ Φ g q)) (hconv g)
    simp only [ofReal_norm] at this
    change ∑' q, ‖term P Γ₂ Φ g q‖ₑ ≠ ⊤
    rw [← this]
    exact ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ∑ a ∈ A, ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j) with hB
  have hδ : ∀ x, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ = S (i (h, x)) := fun x => by
    change _ = ∑' q, ‖term P Γ₂ Φ (i (h, x)) q‖ₑ
    rw [← (Equiv.ofBijective _ hr).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [Equiv.ofBijective_apply, term_mk hΦ, hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hbd : ∀ x, S (i (h, x)) ≤ B := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl, hCx⟩ := hC x
    have e : i (h, γ * a * k) = i (1, γ) * (i (h, a) * i (1, k)) := by
      simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    have hγ2 : i (1, γ) ∈ Γ₂ := hri ⟨γ, hγ⟩ ▸ (r ⟨γ, hγ⟩).2
    change ∑' q, ‖term P Γ₂ Φ _ q‖ₑ ≤ B
    rw [e, tsum_enorm_term_mul_left hΦ hγ2]
    refine (cosetSum_norm_expansion hexp _ (hKK k hk)).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j))
      (fun _ _ => zero_le) ha)
    refine Finset.sum_le_sum fun j _ => mul_le_mul_left ?_ _
    have := hM a j (γ * a * k)
    rw [hCx a j, if_pos rfl] at this
    rw [enorm_le_iff_norm_le, Complex.norm_real, Real.norm_eq_abs]
    exact this.trans (le_abs_self M)
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top enorm_ne_top (hSfin _)
  have hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBfin (measure_lt_top_of_cover h𝓕 hKc A hcov).ne) ?_
    calc ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, B ∂μ :=
          lintegral_mono fun x => (hδ x).trans_le (hbd x)
      _ = B * μ 𝓕 := setLIntegral_const 𝓕 B
  exact unfold_core i h𝓕 hΦ hri hr hlaw hw hwΓ hw1 hwc.aestronglyMeasurable hm h hfin

theorem holValueAt_integral (hi : Continuous i) (hΓ₂ : ∀ γ ∈ Γ, i (1, γ) ∈ Γ₂) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : ℂ → G₂ → ℂ} {σ : ℝ} (hΦ : ∀ s : ℂ, σ < s.re → LeftInv (P ⊓ Γ₂) (Φ s)) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ s : ℂ, σ < s.re → ∀ g, ∀ k ∈ K₂, Φ s (g * k) = ∑ j, cc j k * Φ s (g * kk j))
    (hconv : ∀ s : ℂ, σ < s.re → ∀ g, CosetConv P Γ₂ (Φ s) g) {w : G → ℂ} (hwc : Continuous w)
    (hw1 : ∀ x, ‖w x‖ = 1) {s₀ : ℂ} {Ψ : G₂ → ℂ} (hΨ : ∀ g, HolValueAt (fun s => cosetSum P Γ₂ (Φ s) g) s₀ (Ψ g))
    (h : G) :
    IntegrableOn (fun x => Ψ (i (h, x)) * w x) 𝓕 μ ∧
      HolValueAt (fun s => ∫ x in 𝓕, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x ∂μ) s₀ (∫ x in 𝓕, Ψ (i (h, x)) * w x ∂μ) := by
  classical
  obtain ⟨C, hCm, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top_of_cover h𝓕 hKc A hcov).ne
  have hc : ∀ p : {a // a ∈ A} × ι, Integrable (fun x => C p.1 p.2 x * w x) (μ.restrict 𝓕) := fun p =>
    Integrable.of_bound ((hCm p.1 p.2).aestronglyMeasurable.mul hwc.aestronglyMeasurable) M
      (Eventually.of_forall fun x => by rw [norm_mul, hw1, mul_one]; exact hM _ _ x)
  have hexp' : ∀ s : ℂ, σ < s.re → ∀ x, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x =
      ∑ p : {a // a ∈ A} × ι, C p.1 p.2 x * w x * cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2) := by
    intro s hs x
    obtain ⟨a, ha, γ, hγ, k, hk, hx, hCx⟩ := hC x
    have e : i (h, x) = i (1, γ) * (i (h, a) * i (1, k)) := by
      rw [hx]; simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    rw [e, leftInv_cosetSum (hΦ s hs) _ (hΓ₂ γ hγ),
      cosetSum_expansion (hexp s hs) _ (fun j => hconv s hs _) (hKK k hk), Fintype.sum_prod_type,
      Finset.sum_eq_single (⟨a, ha⟩ : {a // a ∈ A}) (fun b _ hb => by
        simp [hCx, show (b : G) ≠ a from fun e => hb (Subtype.ext e)]) (by simp), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hCx, if_pos rfl]; ring
  have key := holValueAt_integral_of_expansion (ν := μ.restrict 𝓕) (X := G) (ι := {a // a ∈ A} × ι)
    (Φ := fun s x => cosetSum P Γ₂ (Φ s) (i (h, x)) * w x) (Ψ := fun x => Ψ (i (h, x)) * w x)
    (c := fun p x => C p.1 p.2 x * w x) (v := fun p s => cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2))
    (w := fun p => Ψ (i (h, p.1) * kk p.2)) (σ := σ) hc hexp' (fun p => hΨ _)
    (fun x => (hΨ _).mul (holValueAt_const _ _))
  exact ⟨key.2.1, key.2.2⟩

end Main

section Flat

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {δ : P →* ℝ≥0} {χ : P →* Circle} {f : G₂ → ℂ} {ρ s₀ : ℂ}

end Flat

end GlobalTheory.DefDoubling
