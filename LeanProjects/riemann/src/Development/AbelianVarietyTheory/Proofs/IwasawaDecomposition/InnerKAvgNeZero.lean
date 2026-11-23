import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum.KCoef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem toMK_mem_UJ (k : KG ε) : toMK k ∈ UJset ε := K_le_UJ (toMK_mem_K k)

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (w : H) : Continuous fun k : KG ε => σ (toMK k) w :=
  (hσ.2.2 w).comp_continuous (continuous_toMK ε) toMK_mem_UJ

theorem integrable_avg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (w : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) w) (muK ε) :=
  (he.smul (continuous_orbit hσ w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem sigma_K_mul (hσ : IsURepOn (UJset ε) σ) (a b : KG ε) (w : H) :
    σ (toMK (a * b)) w = σ (toMK a) (σ (toMK b) w) :=
  sigma_mul hσ (toMK_mem_UJ a) (toMK_mem_UJ b) w

theorem inner_K (hσ : IsURepOn (UJset ε) σ) (a : KG ε) (x w : H) :
    ⟪σ (toMK a) w, x⟫_ℂ = ⟪w, σ (toMK a⁻¹) x⟫_ℂ := by
  have h := LinearIsometry.inner_map_map ⟨(σ (toMK a) : H →ₗ[ℂ] H), hσ.2.1 _ (toMK_mem_UJ a)⟩ w (σ (toMK a⁻¹) x)
  have e : σ (toMK a) (σ (toMK a⁻¹) x) = x := by
    rw [← sigma_K_mul hσ, mul_inv_cancel]; exact sigma_one hσ x
  rw [← h]
  exact congrArg (fun z => ⟪σ (toMK a) w, z⟫_ℂ) e.symm

theorem kFinFun_coef (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : IsKFin ε σ y) :
    KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) := by
  obtain ⟨S, hS, hyS, hK⟩ := hy
  let φ : H → H → KG ε → ℂ := fun s s' k => ⟪σ (toMK k) s', s⟫_ℂ
  obtain ⟨t, ht⟩ : S.FG := Module.Finite.iff_fg.1 hS
  have hfin : (Set.image2 φ (t : Set H) (t : Set H)).Finite := t.finite_toSet.image2 _ t.finite_toSet
  have key : ∀ s ∈ S, ∀ s' ∈ S, φ s s' ∈ Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)) := by
    intro s hs s' hs'
    rw [← ht] at hs hs'
    induction hs using Submodule.span_induction with
    | mem x hx =>
      induction hs' using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span (Set.mem_image2_of_mem hx hz)
      | zero =>
        have : φ x 0 = 0 := by ext k; simp [φ]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : φ x (a + b) = φ x a + φ x b := by ext k; simp [φ, inner_add_left]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : φ x (c • a) = (starRingEnd ℂ c) • φ x a := by ext k; simp [φ, inner_smul_left, mul_comm]
        rw [this]; exact Submodule.smul_mem _ _ ha
    | zero =>
      have : φ 0 s' = 0 := by ext k; simp [φ]
      rw [this]; exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
      have : φ (a + b) s' = φ a s' + φ b s' := by ext k; simp [φ, inner_add_right]
      rw [this]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : φ (c • a) s' = c • φ a s' := by ext k; simp [φ, inner_smul_right]
      rw [this]; exact Submodule.smul_mem _ _ ha
  have htS : ∀ x ∈ (t : Set H), x ∈ S := fun x hx => ht ▸ Submodule.subset_span hx
  refine ⟨Submodule.span ℂ (Set.image2 φ (t : Set H) (t : Set H)), FiniteDimensional.span_of_finite ℂ hfin, ?_, ?_, ?_⟩
  · have : (fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ) = φ y y := by
      ext k; exact inner_conj_symm _ _
    rw [this]; exact key y hyS y hyS
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, b, -, rfl⟩ := hx
      exact (continuous_orbit hσ b).inner continuous_const
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  · intro ψ hψ k₀
    induction hψ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      constructor
      · have : (fun k => φ a b (k₀ * k)) = φ (σ (toMK k₀⁻¹) a) b := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ, inner_K hσ]
        rw [this]; exact key _ (hK _ (toMK_mem_K _) _ (htS a ha)) _ (htS b hb)
      · have : (fun k => φ a b (k * k₀)) = φ a (σ (toMK k₀) b) := by
          ext k; simp only [φ]; rw [sigma_K_mul hσ]
        rw [this]; exact key _ (htS a ha) _ (hK _ (toMK_mem_K _) _ (htS b hb))
    | zero => exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
    | add a b _ _ ha hb => exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
    | smul c a _ ha => exact ⟨Submodule.smul_mem _ c ha.1, Submodule.smul_mem _ c ha.2⟩

variable [CompleteSpace H]

theorem inner_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) (x w : H) :
    ⟪x, kAvg ε σ e w⟫_ℂ = ∫ k, e k * ⟪x, σ (toMK k) w⟫_ℂ ∂(muK ε) := by
  rw [kAvg, ← integral_inner (integrable_avg hσ he w)]
  simp only [inner_smul_right]

theorem inner_kAvg_ne_zero (hσ : IsURepOn (UJset ε) σ) {y : H} (hy : y ≠ 0) :
    ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0 := by
  have hc : Continuous fun k : KG ε => ⟪y, σ (toMK k) y⟫_ℂ := continuous_const.inner (continuous_orbit hσ y)
  rw [inner_kAvg hσ hc.star]
  have e : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  simp only [e]
  rw [integral_complex_ofReal]
  have hpos : 0 < ∫ k : KG ε, ‖⟪y, σ (toMK k) y⟫_ℂ‖ ^ 2 ∂(muK ε) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (hc.norm.pow 2)
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_
    have : σ (toMK (1 : KG ε)) y = y := sigma_one hσ y
    rw [this]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hy))
  exact_mod_cast hpos.ne'

omit [CompleteSpace H] in

theorem exists_clm_kAvg (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w := by
  let L : H →ₗ[ℂ] H :=
    { toFun := kAvg ε σ e
      map_add' := fun x y => by
        simp only [kAvg, map_add, smul_add]
        exact integral_add (integrable_avg hσ he x) (integrable_avg hσ he y)
      map_smul' := fun c x => by
        simp only [kAvg, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂(muK ε)) fun w => ?_, fun w => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, fun k : KG ε => hσ.2.1 _ (toMK_mem_UJ k) w]
  exact integral_mul_const _ _

theorem kAvg_mem (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) {S : Submodule ℂ H}
    [FiniteDimensional ℂ S] (hK : IsKStableOn ε σ S) {z : H} (hz : z ∈ S) : kAvg ε σ e z ∈ S := by
  rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  rw [inner_kAvg hσ he]
  have : ∀ k : KG ε, ⟪u, σ (toMK k) z⟫_ℂ = 0 := fun k =>
    Submodule.inner_left_of_mem_orthogonal (hK _ (toMK_mem_K k) z hz) hu
  simp [this]

end GlobalTheory.TypeSum.KCoef

namespace GlobalTheory.TypeSum

theorem kCoef_kAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ y, IsKFin ε σ y → KFinFun ε (fun k => star ⟪y, σ (toMK k) y⟫_ℂ)) ∧ (∀ y : H, y ≠ 0 → ⟪y, kAvg ε σ (fun k => star ⟪y, σ (toMK k) y⟫_ℂ) y⟫_ℂ ≠ 0) ∧ (∀ e : KG ε → ℂ, Continuous e → ∃ Q : H →L[ℂ] H, ∀ w, Q w = kAvg ε σ e w) ∧ ∀ e : KG ε → ℂ, Continuous e → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S → ∀ z ∈ S, kAvg ε σ e z ∈ S :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hy => KCoef.kFinFun_coef hσ hy, fun _ hy => KCoef.inner_kAvg_ne_zero hσ hy,
    fun _ he => KCoef.exists_clm_kAvg hσ he, fun _ he _ _ hK _ hz => KCoef.kAvg_mem hσ he hK hz⟩

end GlobalTheory.TypeSum
