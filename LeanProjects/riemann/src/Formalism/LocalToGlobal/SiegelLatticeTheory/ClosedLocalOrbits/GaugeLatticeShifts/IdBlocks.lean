import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat

noncomputable section

open scoped Classical ComplexConjugate ENNReal InnerProductSpace
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix

namespace Formalism.L2.SG.TermOp.IdBlocks

section Schur

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def IrrOn (H : Set G) (π : G → (V →L[ℂ] V)) : Prop :=
  ∀ U : Submodule ℂ V, (∀ h ∈ H, ∀ x ∈ U, π h x ∈ U) → U = ⊥ ∨ U = ⊤

theorem schur_scalar (H : Set G) (π : G → (V →L[ℂ] V)) (hirr : IrrOn H π) (T : V →ₗ[ℂ] V)
    (hT : ∀ h ∈ H, ∀ x, T (π h x) = π h (T x)) : ∃ c : ℂ, ∀ x, T x = c • x := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun x => Subsingleton.elim _ _⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, fun x => ?_⟩
  have hinv : ∀ h ∈ H, ∀ y ∈ Module.End.eigenspace T c, π h y ∈ Module.End.eigenspace T c := by
    intro h hh y hy
    rw [Module.End.mem_eigenspace_iff] at hy ⊢
    rw [hT h hh, hy, map_smul]
  rcases hirr _ hinv with h0 | h1
  · exact absurd h0 (Module.End.hasEigenvalue_iff.1 hc)
  · have : x ∈ Module.End.eigenspace T c := h1 ▸ Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.1 this

end Schur

section Avg

variable {G V : Type*} [Group G] [MeasurableSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

theorem schur_avg (H : Set G) (π : G → (V →L[ℂ] V)) (μ : Measure G) [IsFiniteMeasure μ]
    (hc : μ Hᶜ = 0) (hm : ∀ g ∈ H, ∀ h ∈ H, π (g * h) = π g * π h)
    (hu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (hi : ∀ g ∈ H, μ.map (fun x => g * x) = μ)
    (hmeas : ∀ g : G, Measurable (fun x : G => g * x)) (hs : ∀ x, AEStronglyMeasurable (fun g => π g x) μ)
    (hirr : IrrOn H π) (w ξ : V) :
    ∫ g, ‖⟪π g w, ξ⟫_ℂ‖ ^ 2 ∂μ = μ.real Set.univ * ‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ V := by
  have hae : ∀ᵐ g ∂μ, g ∈ H := by
    rw [ae_iff]; exact hc
  have hnorm : ∀ g ∈ H, ‖π g w‖ = ‖w‖ := fun g hg => by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hu g hg]
  let F : V → G → V := fun x g => ⟪π g w, x⟫_ℂ • π g w
  have hFm : ∀ x, AEStronglyMeasurable (F x) μ := fun x =>
    ((hs w).inner aestronglyMeasurable_const).smul (hs w)
  have hFi : ∀ x, Integrable (F x) μ := by
    intro x
    refine Integrable.of_bound (hFm x) (‖w‖ * ‖x‖ * ‖w‖) ?_
    filter_upwards [hae] with g hg
    calc ‖F x g‖ = ‖⟪π g w, x⟫_ℂ‖ * ‖π g w‖ := norm_smul _ _
      _ ≤ ‖π g w‖ * ‖x‖ * ‖π g w‖ := by gcongr; exact norm_inner_le_norm _ _
      _ = _ := by rw [hnorm g hg]
  let T : V →ₗ[ℂ] V :=
    { toFun := fun x => ∫ g, F x g ∂μ
      map_add' := by
        intro x y
        rw [← integral_add (hFi x) (hFi y)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [F, inner_add_right, add_smul]
      map_smul' := by
        intro c x
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [F, inner_smul_right, mul_smul] }
  have hT : ∀ x, T x = ∫ g, F x g ∂μ := fun x => rfl
  have hcomm : ∀ k ∈ H, ∀ x, T (π k x) = π k (T x) := by
    intro k hk x
    rw [hT, hT, ← (π k).integral_comp_comm (hFi x)]
    have h1 : ∫ g, π k (F x g) ∂μ = ∫ g, F (π k x) (k * g) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with g hg
      simp only [F, map_smul]
      rw [hm k hk g hg]
      show _ = ⟪π k (π g w), π k x⟫_ℂ • π k (π g w)
      rw [hu k hk]
    rw [h1, ← integral_map (hmeas k).aemeasurable (by rw [hi k hk]; exact hFm (π k x)), hi k hk]
  obtain ⟨c, hcT⟩ := schur_scalar H π hirr T hcomm
  have hq : ∀ x, ⟪x, T x⟫_ℂ = ((∫ g, ‖⟪π g w, x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro x
    rw [hT, ← integral_inner (hFi x), ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [F, inner_smul_right]
    rw [← inner_conj_symm x (π g w), Complex.mul_conj']
    push_cast; ring
  have hbd : ∀ x, Integrable (fun g => ‖⟪π g w, x⟫_ℂ‖ ^ 2) μ := by
    intro x
    refine Integrable.of_bound (((hs w).inner aestronglyMeasurable_const).norm.pow 2) ((‖w‖ * ‖x‖) ^ 2) ?_
    filter_upwards [hae] with g hg
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := norm_inner_le_norm (𝕜 := ℂ) (π g w) x
    rw [hnorm g hg] at this
    gcongr

  set b := stdOrthonormalBasis ℂ V
  have htr : (c * Module.finrank ℂ V : ℂ) = ((μ.real Set.univ * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∀ i, ⟪b i, T (b i)⟫_ℂ = c := by
      intro i; rw [hcT, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
    have e2 : ∑ i, ⟪b i, T (b i)⟫_ℂ = c * Module.finrank ℂ V := by
      simp only [e1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    rw [← e2]
    simp only [hq]
    rw [← Complex.ofReal_sum, ← integral_finsetSum _ (fun i _ => hbd (b i))]
    congr 1
    have : ∀ g, ∑ i, ‖⟪π g w, b i⟫_ℂ‖ ^ 2 = ‖π g w‖ ^ 2 := by
      intro g
      simp_rw [norm_inner_symm (π g w)]
      exact b.sum_sq_norm_inner_right (π g w)
    simp_rw [this]
    rw [integral_congr_ae (g := fun _ => ‖w‖ ^ 2) (by filter_upwards [hae] with g hg; rw [hnorm g hg])]
    simp [Measure.real]
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with hd | hd
  · have : Subsingleton V := Module.finrank_zero_iff.1 hd
    rw [Subsingleton.elim ξ 0]; simp [hd]
  · have hq2 := hq ξ
    rw [hcT, inner_smul_right, inner_self_eq_norm_sq_to_K] at hq2
    have hdn : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hc' : c = ((μ.real Set.univ * ‖w‖ ^ 2 : ℝ) : ℂ) / Module.finrank ℂ V := by
      rw [← htr]; field_simp
    rw [hc'] at hq2
    have e : ((μ.real Set.univ * ‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ V : ℝ) : ℂ) =
        ((μ.real Set.univ * ‖w‖ ^ 2 : ℝ) : ℂ) / (Module.finrank ℂ V : ℂ) * ((‖ξ‖ : ℂ) ^ 2) := by
      push_cast; ring
    exact_mod_cast (hq2.symm.trans e.symm)

end Avg

section Fund

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

def IsFundL (Γ Ω : Set G) : Prop :=
  MeasurableSet Ω ∧ (∀ x, ∃ s ∈ Γ, s * x ∈ Ω) ∧ ∀ x ∈ Ω, ∀ s ∈ Γ, s * x ∈ Ω → s = 1

theorem measure_decomp (Γ P Q : Set G) (μ : Measure G) (hc : Γ.Countable) (hP : MeasurableSet P)
    (hQ : MeasurableSet Q) (hex : ∀ n, ∃ a ∈ Γ, a * n ∈ Q)
    (hun : ∀ n, ∀ a ∈ Γ, ∀ a' ∈ Γ, a * n ∈ Q → a' * n ∈ Q → a = a') :
    μ P = ∑' a : Γ, μ (P ∩ {n | (a : G) * n ∈ Q}) := by
  haveI : Countable Γ := hc.to_subtype
  have hU : P = ⋃ a : Γ, P ∩ {n | (a : G) * n ∈ Q} := by
    ext n
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hn
      obtain ⟨a, ha, haQ⟩ := hex n
      exact ⟨⟨a, ha⟩, hn, haQ⟩
    · rintro ⟨a, hn, _⟩
      exact hn
  conv_lhs => rw [hU]
  refine measure_iUnion ?_ (fun a => hP.inter ((measurable_const_mul (a : G)) hQ))
  intro a b hab
  refine Set.disjoint_left.2 fun n h1 h2 => hab ?_
  exact Subtype.ext (hun n a a.2 b b.2 h1.2 h2.2)

theorem fund_vol (Γ Ω : Set G) (μ : Measure G) (hc : Γ.Countable)
    (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (hinv : ∀ a ∈ Γ, a⁻¹ ∈ Γ)
    (hi : ∀ a ∈ Γ, μ.map (fun x => a * x) = μ) (hΩ : IsFundL Γ Ω) (y : G) :
    μ {n | n * y ∈ Ω} = μ Ω := by
  set A : Set G := {n | n * y ∈ Ω}
  have hA : MeasurableSet A := (measurable_mul_const y) hΩ.1
  have hexA : ∀ m, ∃ b ∈ Γ, b * m ∈ A := by
    intro m
    obtain ⟨s, hs, h⟩ := hΩ.2.1 (m * y)
    exact ⟨s, hs, by simpa [A, mul_assoc] using h⟩
  have hunA : ∀ m, ∀ b ∈ Γ, ∀ b' ∈ Γ, b * m ∈ A → b' * m ∈ A → b = b' := by
    intro m b hb b' hb' h1 h2
    have h3 : (b' * b⁻¹) * (b * m * y) ∈ Ω := by
      simpa [A, mul_assoc] using h2
    have := hΩ.2.2 _ h1 _ (hmul _ hb' _ (hinv _ hb)) h3
    exact (mul_inv_eq_one.1 this).symm
  have hunB : ∀ n, ∀ a ∈ Γ, ∀ a' ∈ Γ, a * n ∈ Ω → a' * n ∈ Ω → a = a' := by
    intro n a ha a' ha' h1 h2
    have h3 : (a' * a⁻¹) * (a * n) ∈ Ω := by simpa [mul_assoc] using h2
    have := hΩ.2.2 _ h1 _ (hmul _ ha' _ (hinv _ ha)) h3
    exact (mul_inv_eq_one.1 this).symm
  rw [measure_decomp Γ A Ω μ hc hA hΩ.1 hΩ.2.1 hunB, measure_decomp Γ Ω A μ hc hΩ.1 hA hexA hunA]
  have hterm : ∀ a : Γ, μ (A ∩ {n | (a : G) * n ∈ Ω}) = μ (Ω ∩ {m | (a : G)⁻¹ * m ∈ A}) := by
    intro a
    have hS : MeasurableSet (Ω ∩ {m | (a : G)⁻¹ * m ∈ A}) := hΩ.1.inter ((measurable_const_mul _) hA)
    have := Measure.map_apply (μ := μ) (measurable_const_mul (a : G)) hS
    rw [hi a a.2] at this
    rw [this]
    congr 1
    ext n
    simp [A, and_comm]
  simp_rw [hterm]
  let e : Γ ≃ Γ := ⟨fun a => ⟨(a : G)⁻¹, hinv a a.2⟩, fun a => ⟨(a : G)⁻¹, hinv a a.2⟩,
    fun a => by simp, fun a => by simp⟩
  exact (e.tsum_eq (fun b : Γ => μ (Ω ∩ {m | (b : G) * m ∈ A}))).symm.trans rfl |>.symm ▸ rfl

end Fund

section Unfold

variable {G V : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [TopologicalSpace G]
  [OpensMeasurableSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem integrable_sq (H : Set G) (π : G → (V →L[ℂ] V)) (μ : Measure G) [IsFiniteMeasure μ]
    (hc : μ Hᶜ = 0) (hu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hs : ∀ x, AEStronglyMeasurable (fun g => π g x) μ) (w ξ : V) :
    Integrable (fun g => ‖⟪π g w, ξ⟫_ℂ‖ ^ 2) μ := by
  have hae : ∀ᵐ g ∂μ, g ∈ H := by rw [ae_iff]; exact hc
  refine Integrable.of_bound (((hs w).inner aestronglyMeasurable_const).norm.pow 2) ((‖w‖ * ‖ξ‖) ^ 2) ?_
  filter_upwards [hae] with g hg
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := norm_inner_le_norm (𝕜 := ℂ) (π g w) ξ
  rw [show ‖π g w‖ = ‖w‖ by rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hu g hg]] at this
  gcongr

theorem unfold_sq (μG μN μH ν : Measure G) [SFinite μN] [IsFiniteMeasure μH]
    (S N H Γ Ω : Set G) (π : G → (V →L[ℂ] V)) (ψ : G → ℂ) (W : G → V)
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μN.prod μH).map (fun p => p.1 * p.2))) ∂ν)
    (hNS : N ⊆ S) (hHS : H ⊆ S) (hNH : ∀ n ∈ N, ∀ h ∈ H, n * h ∈ S)
    (hπm : ∀ a ∈ S, ∀ b ∈ S, π (a * b) = π a * π b) (hπN : ∀ n ∈ N, π n = 1)
    (hπu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (hψ : ∀ s ∈ S, ‖ψ s‖ = 1)
    (hW : ∀ s ∈ S, ∀ x, W (s * x) = ψ s • π s (W x)) (hWc : Continuous W)
    (hN : μN Nᶜ = 0) (hH : μH Hᶜ = 0) (hHi : ∀ g ∈ H, μH.map (fun x => g * x) = μH)
    (hπs : ∀ x, AEStronglyMeasurable (fun g => π g x) μH) (hirr : IrrOn H π)
    (hc : Γ.Countable) (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (hinv : ∀ a ∈ Γ, a⁻¹ ∈ Γ)
    (hNi : ∀ a ∈ Γ, μN.map (fun x => a * x) = μN) (hΩ : IsFundL Γ Ω) (ξ : V) :
    ∫⁻ x in Ω, ‖⟪W x, ξ⟫_ℂ‖ₑ ^ 2 ∂μG =
      μN Ω * ENNReal.ofReal (μH.real Set.univ * ‖ξ‖ ^ 2 / Module.finrank ℂ V) * ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν := by
  set c := ENNReal.ofReal (μH.real Set.univ * ‖ξ‖ ^ 2 / Module.finrank ℂ V) with hcdef
  set q : V → ℝ≥0∞ := fun v => ‖⟪v, ξ⟫_ℂ‖ₑ ^ 2 with hqdef
  have hq : Continuous q := (ENNReal.continuous_pow 2).comp (continuous_id.inner continuous_const).enorm
  set f : G → ℝ≥0∞ := Ω.indicator (fun x => q (W x)) with hfdef
  have hf : Measurable f := ((hq.comp hWc).measurable).indicator hΩ.1
  have hψq : ∀ s ∈ S, ∀ v, q (ψ s • v) = q v := by
    intro s hs v
    simp only [q]
    rw [← ofReal_norm, ← ofReal_norm, inner_smul_left, norm_mul, RCLike.norm_conj, hψ s hs, one_mul]
  have hqv : ∀ w : V, ∫⁻ h, q (π h w) ∂μH = c * ‖w‖ₑ ^ 2 := by
    intro w
    have hi := integrable_sq H π μH hH hπu hπs w ξ
    have e0 : ∀ h, q (π h w) = ENNReal.ofReal (‖⟪π h w, ξ⟫_ℂ‖ ^ 2) := by
      intro h; simp only [q]; rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    simp_rw [e0]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun _ => by positivity),
      schur_avg H π μH hH (fun a ha b hb => hπm a (hHS ha) b (hHS hb)) hπu hHi
        (fun g => measurable_const_mul g) hπs hirr w ξ]
    rw [hcdef, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [← lintegral_indicator hΩ.1, hweil f hf]
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((μN.prod μH).map (fun p => p.1 * p.2)) = μN Ω * (c * ‖W x‖ₑ ^ 2) := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x)) (hf.comp (measurable_mul_const x)) measurable_mul]
    rw [lintegral_prod_symm (f := fun a : G × G => f (a.1 * a.2 * x)) ((hf.comp (measurable_mul_const x)).comp measurable_mul).aemeasurable]
    have hHa : ∀ᵐ h ∂μH, h ∈ H := by rw [ae_iff]; exact hH
    have hNa : ∀ᵐ n ∂μN, n ∈ N := by rw [ae_iff]; exact hN
    have hae : ∀ᵐ h ∂μH, ∫⁻ n, f (n * h * x) ∂μN = μN Ω * q (π h (W x)) := by
      filter_upwards [hHa] with h hh
      have e1 : ∀ᵐ n ∂μN, f (n * h * x) = {n | n * (h * x) ∈ Ω}.indicator (fun _ => q (π h (W x))) n := by
        filter_upwards [hNa] with n hn
        have hnh : n * h ∈ S := hNH n hn h hh
        have hmem : (n ∈ {n | n * (h * x) ∈ Ω}) ↔ n * h * x ∈ Ω := by simp [mul_assoc]
        by_cases h1 : n * h * x ∈ Ω
        · rw [Set.indicator_of_mem (hmem.2 h1), hfdef, Set.indicator_of_mem h1]
          show q (W (n * h * x)) = q (π h (W x))
          rw [hW _ hnh, hψq _ hnh, hπm _ (hNS hn) _ (hHS hh), hπN n hn, one_mul]
        · rw [Set.indicator_of_notMem (fun h2 => h1 (hmem.1 h2)), hfdef, Set.indicator_of_notMem h1]
      rw [lintegral_congr_ae e1, lintegral_indicator_const (s := {n | n * (h * x) ∈ Ω}) ((measurable_mul_const (h * x)) hΩ.1),
        fund_vol Γ Ω μN hc hmul hinv hNi hΩ, mul_comm]
    have hqs : AEMeasurable (fun h => q (π h (W x))) μH :=
      (hq.comp_aestronglyMeasurable (hπs (W x))).aemeasurable
    rw [lintegral_congr_ae hae, lintegral_const_mul'' _ hqs, hqv]
  simp_rw [hin]
  have hm : Measurable (fun x => ‖W x‖ₑ ^ 2) := hWc.enorm.measurable.pow_const 2
  rw [lintegral_const_mul _ (hm.const_mul c), lintegral_const_mul _ hm, mul_assoc]

end Unfold

section OOEq

variable {G V : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [TopologicalSpace G]
  [OpensMeasurableSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem eq_smul_of_inner (A : V →L[ℂ] V) (c : ℝ) (h : ∀ ξ, ⟪ξ, A ξ⟫_ℂ = ((c * ‖ξ‖ ^ 2 : ℝ) : ℂ)) :
    A = (c : ℂ) • ContinuousLinearMap.id ℂ V := by
  have h0 : ((A - (c : ℂ) • ContinuousLinearMap.id ℂ V : V →L[ℂ] V) : V →ₗ[ℂ] V) = 0 := by
    refine (inner_map_self_eq_zero _).1 fun x => ?_
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id',
      ContinuousLinearMap.coe_coe, Pi.sub_apply, Pi.smul_apply, id, inner_sub_left, inner_smul_left]
    rw [← inner_conj_symm (A x) x, h x, inner_self_eq_norm_sq_to_K, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    exact sub_self _
  ext x
  have := LinearMap.congr_fun h0 x
  simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_coe, Pi.sub_apply, LinearMap.zero_apply,
    sub_eq_zero] at this
  exact this

theorem oo_eq (μG μN μH ν : Measure G) [SFinite μN] [IsFiniteMeasure μH]
    (S N H Γ Ω : Set G) (π : G → (V →L[ℂ] V)) (ψ : G → ℂ) (W : G → V)
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μN.prod μH).map (fun p => p.1 * p.2))) ∂ν)
    (hNS : N ⊆ S) (hHS : H ⊆ S) (hNH : ∀ n ∈ N, ∀ h ∈ H, n * h ∈ S)
    (hπm : ∀ a ∈ S, ∀ b ∈ S, π (a * b) = π a * π b) (hπN : ∀ n ∈ N, π n = 1)
    (hπu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (hψ : ∀ s ∈ S, ‖ψ s‖ = 1)
    (hW : ∀ s ∈ S, ∀ x, W (s * x) = ψ s • π s (W x)) (hWc : Continuous W)
    (hN : μN Nᶜ = 0) (hH : μH Hᶜ = 0) (hHi : ∀ g ∈ H, μH.map (fun x => g * x) = μH)
    (hπs : ∀ x, AEStronglyMeasurable (fun g => π g x) μH) (hirr : IrrOn H π)
    (hc : Γ.Countable) (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (hinv : ∀ a ∈ Γ, a⁻¹ ∈ Γ)
    (hNi : ∀ a ∈ Γ, μN.map (fun x => a * x) = μN) (hΩ : IsFundL Γ Ω) (hΩf : μN Ω ≠ ⊤)
    (hWn : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂ν = 1) :
    ∫ x in Ω, (innerSL ℂ (W x)).smulRight (W x) ∂μG =
      ((μN.real Ω * μH.real Set.univ / Module.finrank ℂ V : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  have hU : ∀ ξ : V, ∫⁻ x in Ω, ‖⟪W x, ξ⟫_ℂ‖ₑ ^ 2 ∂μG =
      μN Ω * ENNReal.ofReal (μH.real Set.univ * ‖ξ‖ ^ 2 / Module.finrank ℂ V) := by
    intro ξ
    rw [unfold_sq μG μN μH ν S N H Γ Ω π ψ W hweil hNS hHS hNH hπm hπN hπu hψ hW hWc hN hH hHi hπs hirr
      hc hmul hinv hNi hΩ ξ, hWn, mul_one]
  set F : G → (V →L[ℂ] V) := fun x => (innerSL ℂ (W x)).smulRight (W x) with hFdef
  have hFc : Continuous F := by
    have h1 : Continuous fun x => innerSL ℂ (W x) := (innerSL ℂ).continuous.comp hWc
    exact ((ContinuousLinearMap.smulRightL ℂ V V).continuous.comp h1).clm_apply hWc
  set b := stdOrthonormalBasis ℂ V
  have hpar : ∀ w : V, ‖w‖ₑ ^ 2 = ∑ i, ‖⟪w, b i⟫_ℂ‖ₑ ^ 2 := by
    intro w
    have e := b.sum_sq_norm_inner_right w
    simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← e]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm]
  have hint : Integrable F (μG.restrict Ω) := by
    refine ⟨hFc.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e1 : ∀ x, ‖F x‖ₑ = ‖W x‖ₑ ^ 2 := by
      intro x
      rw [← ofReal_norm, hFdef]
      simp only
      rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, ← sq,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e1, hpar]
    rw [lintegral_finsetSum (f := fun i x => ‖⟪W x, b i⟫_ℂ‖ₑ ^ 2) _ (fun i _ => ((ENNReal.continuous_pow 2).comp
      (hWc.inner continuous_const).enorm).measurable)]
    simp_rw [hU]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.mul_lt_top hΩf.lt_top ENNReal.ofReal_lt_top
  refine eq_smul_of_inner _ _ fun ξ => ?_
  rw [ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap ξ)]
  have e2 : ∀ x, ⟪ξ, F x ξ⟫_ℂ = ((‖⟪W x, ξ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    simp only [hFdef, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
    rw [← inner_conj_symm ξ (W x), Complex.mul_conj']
    push_cast; ring
  simp_rw [e2]
  rw [integral_complex_ofReal]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖⟪W x, ξ⟫_ℂ‖ ^ 2)
    (Filter.Eventually.of_forall fun _ => by positivity)
    (((continuous_pow 2).comp (hWc.inner continuous_const).norm).aestronglyMeasurable)]
  have e3 : ∀ x, ENNReal.ofReal (‖⟪W x, ξ⟫_ℂ‖ ^ 2) = ‖⟪W x, ξ⟫_ℂ‖ₑ ^ 2 := by
    intro x; rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [e3]
  rw [hU, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  simp only [Measure.real]
  ring

end OOEq

section WeilInt

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

theorem weil_nonneg (μG μS ν : Measure G) [SFinite μS]
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν)
    (f : G → ℝ) (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μG) :
    (∀ᵐ x ∂ν, Integrable (fun s => f (s * x)) μS) ∧ Integrable (fun x => ∫ s, f (s * x) ∂μS) ν ∧
      ∫ x, f x ∂μG = ∫ x, ∫ s, f (s * x) ∂μS ∂ν := by
  set F : G → ℝ≥0∞ := fun x => ∫⁻ s, ENNReal.ofReal (f (s * x)) ∂μS with hFdef
  have hFm : Measurable F := by
    have : Measurable (Function.uncurry fun x s => ENNReal.ofReal (f (s * x))) :=
      ENNReal.measurable_ofReal.comp (hf.comp (measurable_snd.mul measurable_fst))
    exact this.lintegral_prod_right'
  have hW := hweil (fun x => ENNReal.ofReal (f x)) (ENNReal.measurable_ofReal.comp hf)
  have hlt : ∫⁻ x, F x ∂ν < ⊤ := by
    show ∫⁻ x, ∫⁻ s, ENNReal.ofReal (f (s * x)) ∂μS ∂ν < ⊤
    rw [← hW]; exact hfi.lintegral_lt_top
  have hae : ∀ᵐ x ∂ν, F x < ⊤ := ae_lt_top hFm hlt.ne
  have hint : ∀ x, ∫ s, f (s * x) ∂μS = (F x).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => h0 _)
      (hf.comp (measurable_mul_const x)).aestronglyMeasurable
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hae] with x hx
    refine ⟨(hf.comp (measurable_mul_const x)).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e : ∀ s, ‖f (s * x)‖ₑ = ENNReal.ofReal (f (s * x)) := fun s => by
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (h0 _)]
    simp_rw [e]
    exact hx
  · simp_rw [hint]
    exact integrable_toReal_of_lintegral_ne_top hFm.aemeasurable hlt.ne
  · simp_rw [hint]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hf.aestronglyMeasurable,
      integral_toReal hFm.aemeasurable hae]
    congr 1

theorem weil_real (μG μS ν : Measure G) [SFinite μS]
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν)
    (f : G → ℝ) (hf : Measurable f) (hfi : Integrable f μG) :
    (∀ᵐ x ∂ν, Integrable (fun s => f (s * x)) μS) ∧ Integrable (fun x => ∫ s, f (s * x) ∂μS) ν ∧
      ∫ x, f x ∂μG = ∫ x, ∫ s, f (s * x) ∂μS ∂ν := by
  obtain ⟨hp1, hp2, hp3⟩ := weil_nonneg μG μS ν hweil (fun x => max (f x) 0) (hf.max measurable_const)
    (fun x => le_max_right _ _) hfi.pos_part
  obtain ⟨hn1, hn2, hn3⟩ := weil_nonneg μG μS ν hweil (fun x => max (-f x) 0) (hf.neg.max measurable_const)
    (fun x => le_max_right _ _) hfi.neg_part
  have hsplit : ∀ y, f y = max (f y) 0 - max (-f y) 0 := fun y => (max_zero_sub_max_neg_zero_eq_self _).symm
  have hin : ∀ᵐ x ∂ν, ∫ s, f (s * x) ∂μS = ∫ s, max (f (s * x)) 0 ∂μS - ∫ s, max (-f (s * x)) 0 ∂μS := by
    filter_upwards [hp1, hn1] with x h1 h2
    rw [← integral_sub h1 h2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun s => hsplit _)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hp1, hn1] with x h1 h2
    exact (h1.sub h2).congr (Filter.Eventually.of_forall fun s => (hsplit _).symm)
  · exact (hp2.sub hn2).congr (hin.mono fun x hx => hx.symm)
  · rw [integral_congr_ae hin, integral_sub hp2 hn2, ← hp3, ← hn3, ← integral_sub hfi.pos_part hfi.neg_part]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hsplit y)

theorem weil_complex (μG μS ν : Measure G) [SFinite μS]
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν)
    (g : G → ℂ) (hg : Measurable g) (hgi : Integrable g μG) :
    (∀ᵐ x ∂ν, Integrable (fun s => g (s * x)) μS) ∧ ∫ x, g x ∂μG = ∫ x, ∫ s, g (s * x) ∂μS ∂ν := by
  obtain ⟨hr1, hr2, hr3⟩ := weil_real μG μS ν hweil (fun x => (g x).re) (Complex.measurable_re.comp hg) hgi.re
  obtain ⟨hi1, hi2, hi3⟩ := weil_real μG μS ν hweil (fun x => (g x).im) (Complex.measurable_im.comp hg) hgi.im
  have h1 : ∀ᵐ x ∂ν, Integrable (fun s => g (s * x)) μS := by
    filter_upwards [hr1, hi1] with x h1 h2
    exact Integrable.re_im_iff.1 ⟨h1, h2⟩
  have hre : ∀ᵐ x ∂ν, (∫ s, g (s * x) ∂μS).re = ∫ s, (g (s * x)).re ∂μS := by
    filter_upwards [h1] with x hx
    exact (integral_re hx).symm
  have him : ∀ᵐ x ∂ν, (∫ s, g (s * x) ∂μS).im = ∫ s, (g (s * x)).im ∂μS := by
    filter_upwards [h1] with x hx
    exact (integral_im hx).symm
  have h2 : Integrable (fun x => ∫ s, g (s * x) ∂μS) ν := by
    refine Integrable.re_im_iff.1 ⟨hr2.congr (hre.mono fun x hx => hx.symm), hi2.congr (him.mono fun x hx => hx.symm)⟩
  refine ⟨h1, Complex.ext ?_ ?_⟩
  · have e1 := integral_re hgi
    have e2 := integral_re h2
    simp only [RCLike.re_to_complex] at e1 e2
    rw [← e1, ← e2, integral_congr_ae hre]
    exact hr3
  · have e1 := integral_im hgi
    have e2 := integral_im h2
    simp only [RCLike.im_to_complex] at e1 e2
    rw [← e1, ← e2, integral_congr_ae him]
    exact hi3

end WeilInt

section Cross

variable {G V V' : Type*} [Group G] [MeasurableSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem schur_cross (H : Set G) (π : G → (V →L[ℂ] V)) (σ : G → (V' →L[ℂ] V')) (μ : Measure G) [IsFiniteMeasure μ]
    (hc : μ Hᶜ = 0) (hm : ∀ g ∈ H, ∀ h ∈ H, π (g * h) = π g * π h)
    (hmσ : ∀ g ∈ H, ∀ h ∈ H, σ (g * h) = σ g * σ h)
    (hu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (huσ : ∀ g ∈ H, ∀ x y, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hi : ∀ g ∈ H, μ.map (fun x => g * x) = μ) (hmeas : ∀ g : G, Measurable (fun x : G => g * x))
    (hs : ∀ x, AEStronglyMeasurable (fun g => π g x) μ) (hsσ : ∀ x, AEStronglyMeasurable (fun g => σ g x) μ)
    (hne : ∀ T : V' →ₗ[ℂ] V, (∀ h ∈ H, ∀ x, T (σ h x) = π h (T x)) → T = 0) (w ξ : V) (w' η : V') :
    ∫ g, starRingEnd ℂ ⟪π g w, ξ⟫_ℂ * ⟪σ g w', η⟫_ℂ ∂μ = 0 := by
  have hae : ∀ᵐ g ∂μ, g ∈ H := by rw [ae_iff]; exact hc
  have hnorm : ∀ g ∈ H, ‖π g w‖ = ‖w‖ := fun g hg => by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hu g hg]
  have hnormσ : ∀ g ∈ H, ‖σ g w'‖ = ‖w'‖ := fun g hg => by
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, huσ g hg]
  let F : V' → G → V := fun x g => ⟪σ g w', x⟫_ℂ • π g w
  have hFm : ∀ x, AEStronglyMeasurable (F x) μ := fun x =>
    ((hsσ w').inner aestronglyMeasurable_const).smul (hs w)
  have hFi : ∀ x, Integrable (F x) μ := by
    intro x
    refine Integrable.of_bound (hFm x) (‖w'‖ * ‖x‖ * ‖w‖) ?_
    filter_upwards [hae] with g hg
    calc ‖F x g‖ = ‖⟪σ g w', x⟫_ℂ‖ * ‖π g w‖ := norm_smul _ _
      _ ≤ ‖σ g w'‖ * ‖x‖ * ‖π g w‖ := by gcongr; exact norm_inner_le_norm _ _
      _ = _ := by rw [hnormσ g hg, hnorm g hg]
  let T : V' →ₗ[ℂ] V :=
    { toFun := fun x => ∫ g, F x g ∂μ
      map_add' := by
        intro x y
        rw [← integral_add (hFi x) (hFi y)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [F, inner_add_right, add_smul]
      map_smul' := by
        intro c x
        rw [RingHom.id_apply, ← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [F, inner_smul_right, mul_smul] }
  have hT : ∀ x, T x = ∫ g, F x g ∂μ := fun x => rfl
  have hcomm : ∀ k ∈ H, ∀ x, T (σ k x) = π k (T x) := by
    intro k hk x
    rw [hT, hT, ← (π k).integral_comp_comm (hFi x)]
    have h1 : ∫ g, π k (F x g) ∂μ = ∫ g, F (σ k x) (k * g) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with g hg
      simp only [F, map_smul]
      rw [hm k hk g hg, hmσ k hk g hg]
      show _ = ⟪σ k (σ g w'), σ k x⟫_ℂ • π k (π g w)
      rw [huσ k hk]
    rw [h1, ← integral_map (hmeas k).aemeasurable (by rw [hi k hk]; exact hFm (σ k x)), hi k hk]
  have hT0 := hne T hcomm
  have h : ⟪ξ, T η⟫_ℂ = 0 := by rw [hT0]; simp
  rw [hT, ← integral_inner (hFi η)] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [F, inner_smul_right]
  rw [inner_conj_symm]
  ring

end Cross

section CrossUnfold

variable {G V V' : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [TopologicalSpace G]
  [OpensMeasurableSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem cross_zero (μG μN μH ν : Measure G) [SFinite μN] [IsFiniteMeasure μH]
    (S N H Γ Ω : Set G) (π : G → (V →L[ℂ] V)) (σ : G → (V' →L[ℂ] V')) (ψ : G → ℂ) (W : G → V) (W' : G → V')
    (hweil : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μN.prod μH).map (fun p => p.1 * p.2))) ∂ν)
    (hNS : N ⊆ S) (hHS : H ⊆ S) (hNH : ∀ n ∈ N, ∀ h ∈ H, n * h ∈ S)
    (hπm : ∀ a ∈ S, ∀ b ∈ S, π (a * b) = π a * π b) (hπN : ∀ n ∈ N, π n = 1)
    (hσm : ∀ a ∈ S, ∀ b ∈ S, σ (a * b) = σ a * σ b) (hσN : ∀ n ∈ N, σ n = 1)
    (hπu : ∀ g ∈ H, ∀ x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ) (hσu : ∀ g ∈ H, ∀ x y, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hψ : ∀ s ∈ S, ‖ψ s‖ = 1)
    (hW : ∀ s ∈ S, ∀ x, W (s * x) = ψ s • π s (W x)) (hW' : ∀ s ∈ S, ∀ x, W' (s * x) = ψ s • σ s (W' x))
    (hWc : Continuous W) (hW'c : Continuous W')
    (hN : μN Nᶜ = 0) (hH : μH Hᶜ = 0) (hHi : ∀ g ∈ H, μH.map (fun x => g * x) = μH)
    (hπs : ∀ x, AEStronglyMeasurable (fun g => π g x) μH) (hσs : ∀ x, AEStronglyMeasurable (fun g => σ g x) μH)
    (hne : ∀ T : V' →ₗ[ℂ] V, (∀ h ∈ H, ∀ x, T (σ h x) = π h (T x)) → T = 0)
    (hc : Γ.Countable) (hmul : ∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) (hinv : ∀ a ∈ Γ, a⁻¹ ∈ Γ)
    (hNi : ∀ a ∈ Γ, μN.map (fun x => a * x) = μN) (hΩ : IsFundL Γ Ω)
    (hint : IntegrableOn (fun x => (innerSL ℂ (W' x)).smulRight (W x)) Ω μG) :
    ∫ x in Ω, (innerSL ℂ (W' x)).smulRight (W x) ∂μG = 0 := by
  ext η
  refine ext_inner_left ℂ fun ξ => ?_
  rw [ContinuousLinearMap.integral_apply hint η, ← integral_inner (hint.apply_continuousLinearMap η) ξ]
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
  set g0 : G → ℂ := fun x => starRingEnd ℂ ⟪W x, ξ⟫_ℂ * ⟪W' x, η⟫_ℂ with hg0
  have e0 : ∀ x, ⟪ξ, ((innerSL ℂ (W' x)).smulRight (W x)) η⟫_ℂ = g0 x := by
    intro x
    simp only [hg0, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
    rw [inner_conj_symm]
    ring
  simp_rw [e0]
  have hg0c : Continuous g0 :=
    (Complex.continuous_conj.comp (hWc.inner continuous_const)).mul (hW'c.inner continuous_const)
  set g : G → ℂ := Ω.indicator g0 with hgdef
  have hgm : Measurable g := hg0c.measurable.indicator hΩ.1
  have hgi : Integrable g μG := by
    refine (integrable_indicator_iff hΩ.1).2 ?_
    have := (hint.apply_continuousLinearMap η).const_inner (𝕜 := ℂ) ξ
    exact this.congr (Filter.Eventually.of_forall fun x => e0 x)
  rw [← integral_indicator hΩ.1]
  obtain ⟨hae, heq⟩ := weil_complex μG ((μN.prod μH).map (fun p => p.1 * p.2)) ν hweil g hgm hgi
  rw [heq]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with x hx
  have hxp : Integrable (fun p : G × G => g (p.1 * p.2 * x)) (μN.prod μH) :=
    (integrable_map_measure hx.1 measurable_mul.aemeasurable).1 hx
  rw [integral_map measurable_mul.aemeasurable hx.1]
  rw [integral_prod_symm (fun p : G × G => g (p.1 * p.2 * x)) hxp]
  have hHa : ∀ᵐ h ∂μH, h ∈ H := by rw [ae_iff]; exact hH
  have hNa : ∀ᵐ n ∂μN, n ∈ N := by rw [ae_iff]; exact hN
  have hin : ∀ᵐ h ∂μH, ∫ n, g (n * h * x) ∂μN =
      (μN Ω).toReal * (starRingEnd ℂ ⟪π h (W x), ξ⟫_ℂ * ⟪σ h (W' x), η⟫_ℂ) := by
    filter_upwards [hHa] with h hh
    have e1 : ∀ᵐ n ∂μN, g (n * h * x) = {n | n * (h * x) ∈ Ω}.indicator
        (fun _ => starRingEnd ℂ ⟪π h (W x), ξ⟫_ℂ * ⟪σ h (W' x), η⟫_ℂ) n := by
      filter_upwards [hNa] with n hn
      have hnh : n * h ∈ S := hNH n hn h hh
      have hmem : (n ∈ {n | n * (h * x) ∈ Ω}) ↔ n * h * x ∈ Ω := by simp [mul_assoc]
      by_cases h1 : n * h * x ∈ Ω
      · rw [Set.indicator_of_mem (hmem.2 h1), hgdef, Set.indicator_of_mem h1]
        simp only [hg0]
        rw [hW _ hnh, hW' _ hnh, hπm _ (hNS hn) _ (hHS hh), hσm _ (hNS hn) _ (hHS hh), hπN n hn, hσN n hn,
          one_mul, one_mul, inner_smul_left, inner_smul_left, map_mul, Complex.conj_conj]
        have hψ1 : ψ (n * h) * starRingEnd ℂ (ψ (n * h)) = 1 := by
          rw [Complex.mul_conj', hψ _ hnh]; simp
        calc ψ (n * h) * starRingEnd ℂ ⟪(π h) (W x), ξ⟫_ℂ * (starRingEnd ℂ (ψ (n * h)) * ⟪(σ h) (W' x), η⟫_ℂ)
            = (ψ (n * h) * starRingEnd ℂ (ψ (n * h))) *
                (starRingEnd ℂ ⟪(π h) (W x), ξ⟫_ℂ * ⟪(σ h) (W' x), η⟫_ℂ) := by ring
          _ = _ := by rw [hψ1, one_mul]
      · rw [Set.indicator_of_notMem (fun h2 => h1 (hmem.1 h2)), hgdef, Set.indicator_of_notMem h1]
    rw [integral_congr_ae e1, integral_indicator_const (s := {n | n * (h * x) ∈ Ω}) _ ((measurable_mul_const (h * x)) hΩ.1),
      Measure.real, fund_vol Γ Ω μN hc hmul hinv hNi hΩ, Complex.real_smul]
  rw [integral_congr_ae hin, integral_const_mul,
    schur_cross H π σ μH hH (fun a ha b hb => hπm a (hHS ha) b (hHS hb)) (fun a ha b hb => hσm a (hHS ha) b (hHS hb))
      hπu hσu hHi (fun g => measurable_const_mul g) hπs hσs hne (W x) ξ (W' x) η, mul_zero]
  rfl

end CrossUnfold

section Diag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

theorem norm_psiR {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) : ‖psiR ε gg e f z g‖ = 1 := by
  unfold psiR
  have hS : ∑ a, (rootCoord ε e f z g a + star (rootCoord ε e f z g a)) =
      ((∑ a, 2 * (rootCoord ε e f z g a).re : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.add_conj]
    push_cast; ring
  rw [hS, show 2 * (Real.pi : ℂ) * Complex.I * (((∑ a, 2 * (rootCoord ε e f z g a).re : ℝ) : ℂ) / (gg : ℂ)) =
      ((2 * Real.pi * ((∑ a, 2 * (rootCoord ε e f z g a).re) / gg) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

variable {D : D7} {X : HidaSetting D}

theorem norm_psiInfU (u : D.what₂.Word) (s : X.B.I.Ginf) : ‖X.psiInfU u s‖ = 1 := by
  simp only [HidaSetting.psiInfU, psiInf, norm_prod, norm_psiR, Finset.prod_const_one]

theorem mulVec_fix {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (h : B *ᵥ x = x) :
    (A * B - 1) *ᵥ x = (A - 1) *ᵥ x := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, h]

theorem nh_mem (u : D.what₂.Word) (n h : X.B.I.Ginf) (hn : n ∈ X.NinfU u) (hh : h ∈ Hinf X u) :
    n * h ∈ X.SinfU u := by
  intro v
  have hm : uMat ((n * h) v) = uMat (n v) * uMat (h v) := by simp [uMat]
  have he : ∀ a, uMat (h v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
    fun a => hh v _ (Or.inl (Or.inl ⟨a, rfl⟩))
  have hz : uMat (h v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) := hh v _ (Or.inr rfl)
  obtain ⟨⟨hne, hnz⟩, _⟩ := hn v
  refine ⟨fun a => ?_, ?_⟩
  · rw [hm, mulVec_fix _ _ _ (he a)]
    exact hne a
  · rw [hm, mulVec_fix _ _ _ hz]
    exact hnz

theorem isClosed_Hinf (u : D.what₂.Word) : IsClosed ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := by
  show IsClosed {s : X.B.I.Ginf | ∀ v, ∀ x ∈ fixSet X u, uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x}
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun v => isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
  exact Continuous.matrix_mulVec ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v))
    continuous_const

theorem piU_aesm (u : D.what₂.Word) (x : X.Vpi u) : AEStronglyMeasurable (fun g => X.piU u g x) (X.muH u) := by
  have hc : ContinuousOn (fun g => X.piU u g x) ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
    ((X.piU_rep u).2.2.2.2 x).mono (fun s hs => hinf_le_sinf X u s hs)
  have hm := hc.aestronglyMeasurable (μ := X.muH u) (isClosed_Hinf u).measurableSet
  have hae : ∀ᵐ g ∂(X.muH u), g ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := by
    rw [ae_iff]; exact (X.muH_haar u).2.2.1
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm

variable (X) in

def PiIrr (u : D.what₂.Word) : Prop := IrrOn ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) (X.piU u)

theorem rk1_smul_right {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (c : ℂ) (w : V') :
    rk1 v (c • w) = starRingEnd ℂ c • rk1 v w := by
  ext ξ
  simp [rankOneInnerOperator_apply, inner_smul_left, smul_smul, mul_comm]

theorem oot_eq {u : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (t : GTerm X u u F0 F0 what₂ what₂)
    (hΩ : IsSFund X.B.I (ROinf t) (FundOf t)) (hγ : t.pt.1⁻¹ ∈ X.NinfU u)
    (hRc : (ROinf t).Countable) (hRm : ∀ a ∈ ROinf t, ∀ b ∈ ROinf t, a * b ∈ ROinf t)
    (hRi : ∀ a ∈ ROinf t, a⁻¹ ∈ ROinf t) (hRN : ROinf t ⊆ X.NinfU u) (hirr : PiIrr X u)
    (hHf : X.muH u Set.univ ≠ ⊤) (hΩf : X.muN u (FundOf t) ≠ ⊤) :
    OOt t = (starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) *
      (((X.muN u).real (FundOf t) * (X.muH u).real Set.univ / Module.finrank ℂ (X.Vpi u) : ℝ) : ℂ)) •
        ContinuousLinearMap.id ℂ (X.Vpi u) := by
  haveI : SigmaFinite (X.muN u) := (X.muN_haar u).1
  haveI : IsFiniteMeasure (X.muH u) := ⟨hHf.lt_top⟩
  have hW : ∀ x, X.Wu u (t.pt.1⁻¹ * x) = X.psiInfU u t.pt.1⁻¹ • X.Wu u x := by
    intro x
    rw [(X.Wu_spec u).1 _ (fun v => (hγ v).1) x]
    have h1 : X.piU u t.pt.1⁻¹ = 1 := (X.piU_rep u).2.2.2.1 _ hγ
    rw [h1]; rfl
  have e1 : OOt t = starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) •
      ∫ x in FundOf t, (innerSL ℂ (X.Wu u x)).smulRight (X.Wu u x) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    unfold OOt OO
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [hW x, rk1_smul_right]
    rfl
  rw [e1, oo_eq (Formalism.L2.SG.ProjRows.muInf X.B.I) (X.muN u) (X.muH u) (X.nuQ u) (X.SinfU u) (X.NinfU u)
    ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) (ROinf t) (FundOf t) (X.piU u) (X.psiInfU u) (X.Wu u)
    (X.nuQ_weil u) (fun s hs v => (hs v).1) (fun s hs => hinf_le_sinf X u s hs) (fun n hn h hh => nh_mem u n h hn hh)
    (X.piU_rep u).2.1 (X.piU_rep u).2.2.2.1
    (fun g hg => (X.piU_rep u).2.2.1 g (hinf_le_sinf X u g hg)) (fun s _ => norm_psiInfU u s)
    (X.Wu_spec u).1 (X.Wu_spec u).2.2.1 (X.muN_haar u).2.2.1 (X.muH_haar u).2.2.1
    (fun g hg => (X.muH_haar u).2.2.2 g hg) (piU_aesm u) hirr hRc hRm hRi
    (fun a ha => (X.muN_haar u).2.2.2 a (hRN ha)) hΩ hΩf (X.Wu_spec u).2.2.2.2, smul_smul]

end Diag

section DiagSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def Meets (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (t : GTerm X u u' F0 F0' what₂ rows')
    (ρ : cs.Cl) (ρ' : cs'.Cl) : Prop :=
  cs.lamOf ρ = t.lam ∧ cs'.lamOf ρ' = t.lam' ∧
    kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2

theorem blk_of_not (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    {t : GTerm X u u' F0 F0' what₂ rows'} {ρ : cs.Cl} {ρ' : cs'.Cl} (h : ¬ Meets cs cs' t ρ ρ') :
    blk cs cs' FdN FdN' t ρ ρ' = 0 := by
  unfold blk; exact if_neg h

theorem blk_of (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    {t : GTerm X u u' F0 F0' what₂ rows'} {ρ : cs.Cl} {ρ' : cs'.Cl} (h : Meets cs cs' t ρ ρ') :
    blk cs cs' FdN FdN' t ρ ρ' = ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) •
      (X.chi2 (kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt) • OOt t) := by
  unfold blk; exact if_pos h

variable (F0) in

def IdMeetOne (cs : ColSys X u what₂) : Prop :=
  (∀ (ρ ρ' : cs.Cl) (t : GTerm X u u F0 F0 what₂ what₂), t.isId → Meets cs cs t ρ ρ' → ρ = ρ') ∧
    (∀ (ρ : cs.Cl) (t t' : GTerm X u u F0 F0 what₂ what₂), t.isId → t'.isId → Meets cs cs t ρ ρ →
      Meets cs cs t' ρ ρ → t = t') ∧
    ∀ ρ : cs.Cl, ∃ t : GTerm X u u F0 F0 what₂ what₂, t.isId ∧ Meets cs cs t ρ ρ

variable (F0) in

def IdMeetPhase (cs : ColSys X u what₂) : Prop :=
  ∀ (ρ : cs.Cl) (t : GTerm X u u F0 F0 what₂ what₂), t.isId → Meets cs cs t ρ ρ →
    t.pt.1⁻¹ ∈ X.NinfU u ∧
      X.chi2 (kOf X u u (cs.h ρ : X.B.I.Gf) (cs.h ρ : X.B.I.Gf) t.pt) * starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1

variable (F0) in

def IdMeetRO (cs : ColSys X u what₂) : Prop :=
  ∀ (ρ : cs.Cl) (t : GTerm X u u F0 F0 what₂ what₂), t.isId → Meets cs cs t ρ ρ →
    (ROinf t).Countable ∧ (∀ a ∈ ROinf t, ∀ b ∈ ROinf t, a * b ∈ ROinf t) ∧ (∀ a ∈ ROinf t, a⁻¹ ∈ ROinf t) ∧
      ROinf t ⊆ X.NinfU u

variable (F0) in

def IdMeetVol (cs : ColSys X u what₂) (FdN : Set X.B.I.Ginf) : Prop :=
  ∀ (ρ : cs.Cl) (t : GTerm X u u F0 F0 what₂ what₂), t.isId → Meets cs cs t ρ ρ →
    X.muN u (FundOf t) = X.muN u FdN

theorem idDiagBlocks_of (cs : ColSys X u what₂) (FdN : Set X.B.I.Ginf) (hK2 : X.LevelSubgroupNormalized)
    (hFE : FundExists X u u F0 F0 what₂ what₂) (hirr : PiIrr X u)
    (hH0 : 0 < (X.muH u Set.univ).toReal) (hN0 : 0 < (X.muN u FdN).toReal)
    (h1 : IdMeetOne F0 cs) (hP : IdMeetPhase F0 cs) (hR : IdMeetRO F0 cs) (hV : IdMeetVol F0 cs FdN) :
    IdDiagBlocks F0 cs FdN := by
  intro _ ρ ρ'
  rcases subsingleton_or_nontrivial (X.Vpi u) with hs | hs
  · have hall : ∀ A B : X.Vpi u →L[ℂ] X.Vpi u, A = B := fun A B => by
      ext x; exact Subsingleton.elim _ _
    rw [hall (if ρ = ρ' then _ else _) 0,
      show (fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => blk cs cs FdN FdN t.1 ρ ρ') = fun _ => 0 from
        funext fun _ => hall _ _]
    exact hasSum_zero
  by_cases hρ : ρ = ρ'
  · subst hρ
    rw [if_pos rfl]
    obtain ⟨t0, ht0, hm0⟩ := h1.2.2 ρ
    have hval : blk cs cs FdN FdN t0 ρ ρ = ContinuousLinearMap.id ℂ (X.Vpi u) := by
      obtain ⟨hγ, hph⟩ := hP ρ t0 ht0 hm0
      obtain ⟨hRc, hRm, hRi, hRN⟩ := hR ρ t0 ht0 hm0
      have hvol := hV ρ t0 ht0 hm0
      have hΩ : IsSFund X.B.I (ROinf t0) (FundOf t0) := by
        have h := hFE t0
        unfold FundOf
        rw [dif_pos h]
        exact h.choose_spec
      have hNf : X.muN u FdN ≠ ⊤ := fun h => by rw [h] at hN0; simp at hN0
      have hHf : X.muH u Set.univ ≠ ⊤ := fun h => by rw [h] at hH0; simp at hH0
      rw [blk_of cs cs FdN FdN hm0, oot_eq t0 hΩ hγ hRc hRm hRi hRN hirr hHf (hvol ▸ hNf), smul_smul, smul_smul]
      have hd : (0 : ℝ) < Module.finrank ℂ (X.Vpi u) := by exact_mod_cast Module.finrank_pos
      have hK : 0 < X.volK2 := ENNReal.toReal_pos hK2.2.2.1.ne' hK2.2.2.2.ne
      have hc0 : 0 < c0X X u FdN := by unfold c0X; positivity
      have hscl : scl FdN FdN (X := X) (u := u) (u' := u) = (c0X X u FdN)⁻¹ := by
        unfold scl; rw [Real.sqrt_mul_self hc0.le]
      set k := X.chi2 (kOf X u u (cs.h ρ : X.B.I.Gf) (cs.h ρ : X.B.I.Gf) t0.pt)
      set ps := starRingEnd ℂ (X.psiInfU u t0.pt.1⁻¹)
      have hcoef : ((scl FdN FdN (X := X) (u := u) (u' := u) * X.volK2 : ℝ) : ℂ) *
          (k * (ps * (((X.muN u).real (FundOf t0) * (X.muH u).real Set.univ /
            Module.finrank ℂ (X.Vpi u) : ℝ) : ℂ))) = 1 := by
        rw [show k * (ps * (((X.muN u).real (FundOf t0) * (X.muH u).real Set.univ /
            Module.finrank ℂ (X.Vpi u) : ℝ) : ℂ)) = (k * ps) * (((X.muN u).real (FundOf t0) *
            (X.muH u).real Set.univ / Module.finrank ℂ (X.Vpi u) : ℝ) : ℂ) by ring, hph, one_mul,
          ← Complex.ofReal_mul, Complex.ofReal_eq_one, hscl]
        simp only [Measure.real, hvol]
        unfold c0X
        field_simp
      rw [mul_assoc, hcoef, one_smul]
    have hz : ∀ t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId}, t ≠ ⟨t0, ht0⟩ →
        blk cs cs FdN FdN t.1 ρ ρ = 0 := by
      intro t ht
      exact blk_of_not _ _ _ _ fun hm => ht (Subtype.ext (h1.2.1 ρ t.1 t0 t.2 ht0 hm hm0))
    have := hasSum_single (f := fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => blk cs cs FdN FdN t.1 ρ ρ)
      ⟨t0, ht0⟩ hz
    simp only at this
    rwa [hval] at this
  · rw [if_neg hρ]
    have hz : (fun t : {t : GTerm X u u F0 F0 what₂ what₂ // t.isId} => blk cs cs FdN FdN t.1 ρ ρ') = fun _ => 0 :=
      funext fun t => blk_of_not _ _ _ _ fun hm => hρ (h1.1 ρ ρ' t.1 t.2 hm)
    rw [hz]
    exact hasSum_zero

end DiagSteps

section ClosedDiag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

def PiIrrC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), PiIrr X u

def NeatC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK

def IdMeetC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    IdMeetOne (X.Fu u) (Y.cs u) ∧ IdMeetPhase (X.Fu u) (Y.cs u) ∧ IdMeetRO (X.Fu u) (Y.cs u) ∧
      IdMeetVol (X.Fu u) (Y.cs u) (Y.FN u)

theorem idDiagBlocksC (hV : VolPosC) (hI : PiIrrC) (hM : IdMeetC) (D : D7) (X : HidaSetting D) (Y : Full X)
    (u : D.what₂.Word) (hC : NeatKu X u Y.hK)
    (hFE : FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) :
    IdDiagBlocks (X.Fu u) (Y.cs u) (Y.FN u) := by
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
  obtain ⟨hN, hH⟩ := hV D X Y u hK2
  obtain ⟨h1, h2, h3, h4⟩ := hM D X Y u hC hFE
  exact idDiagBlocks_of (Y.cs u) (Y.FN u) hK2 hFE (hI D X u) hH
    (pos_of_mul_pos_right hN ENNReal.toReal_nonneg) h1 h2 h3 h4

def IdCellDiagNeatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    Formalism.L2.SG.TermOp.IdCellDiag (X.Fu u) (Y.cs u) (Y.FN u)

theorem idCellDiagNeatC_of (hV : VolPosC) (hI : PiIrrC) (hM : IdMeetC) : IdCellDiagNeatC :=
  fun D X Y u hC hFE => idCellDiag_of (Y.cs u) (Y.FN u) (idDiagBlocksC hV hI hM D X Y u hC hFE)

theorem idCellDiagC_of_steps (hV : VolPosC) (hI : PiIrrC) (hM : IdMeetC) (hN : NeatC) : IdCellDiagC :=
  idCellDiagC_of fun D X Y u _ hFE _ => idDiagBlocksC hV hI hM D X Y u (hN D X Y u) hFE

end ClosedDiag

section Off

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (F0 F0' what₂ rows') in

def IdOffConj : Prop :=
  u ≠ u' → ∀ t : GTerm X u u' F0 F0' what₂ rows', t.isId →
    (∀ s ∈ X.SinfU u, t.pt.1⁻¹ * s * t.pt.1 ∈ X.SinfU u' ∧
      X.psiInfU u' (t.pt.1⁻¹ * s * t.pt.1) = X.psiInfU u s) ∧
    ∀ n ∈ X.NinfU u, t.pt.1⁻¹ * n * t.pt.1 ∈ X.NinfU u'

variable (F0 F0' what₂ rows') in

def IdOffIneq : Prop :=
  u ≠ u' → ∀ t : GTerm X u u' F0 F0' what₂ rows', t.isId →
    ∀ T : X.Vpi u' →ₗ[ℂ] X.Vpi u, (∀ h ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), ∀ x,
      T (X.piU u' (t.pt.1⁻¹ * h * t.pt.1) x) = X.piU u h (T x)) → T = 0

variable (F0 F0' what₂ rows') in

def IdOffRO : Prop :=
  u ≠ u' → ∀ t : GTerm X u u' F0 F0' what₂ rows', t.isId →
    (ROinf t).Countable ∧ (∀ a ∈ ROinf t, ∀ b ∈ ROinf t, a * b ∈ ROinf t) ∧ (∀ a ∈ ROinf t, a⁻¹ ∈ ROinf t) ∧
      ROinf t ⊆ X.NinfU u

theorem oot_off_eq_zero (t : GTerm X u u' F0 F0' what₂ rows') (hΩ : IsSFund X.B.I (ROinf t) (FundOf t))
    (hOI : OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) (FundOf t) (X.Wu u) (X.Wu u') t.pt.1)
    (hHf : X.muH u Set.univ ≠ ⊤)
    (hS : ∀ s ∈ X.SinfU u, t.pt.1⁻¹ * s * t.pt.1 ∈ X.SinfU u' ∧
      X.psiInfU u' (t.pt.1⁻¹ * s * t.pt.1) = X.psiInfU u s)
    (hN : ∀ n ∈ X.NinfU u, t.pt.1⁻¹ * n * t.pt.1 ∈ X.NinfU u')
    (hne : ∀ T : X.Vpi u' →ₗ[ℂ] X.Vpi u, (∀ h ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), ∀ x,
      T (X.piU u' (t.pt.1⁻¹ * h * t.pt.1) x) = X.piU u h (T x)) → T = 0)
    (hRc : (ROinf t).Countable) (hRm : ∀ a ∈ ROinf t, ∀ b ∈ ROinf t, a * b ∈ ROinf t)
    (hRi : ∀ a ∈ ROinf t, a⁻¹ ∈ ROinf t) (hRN : ROinf t ⊆ X.NinfU u) :
    OOt t = 0 := by
  haveI : SigmaFinite (X.muN u) := (X.muN_haar u).1
  haveI : IsFiniteMeasure (X.muH u) := ⟨hHf.lt_top⟩
  set γ := t.pt.1 with hγ
  have hSH : ∀ h ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf), h ∈ X.SinfU u :=
    fun h hh => hinf_le_sinf X u h hh
  have hσs : ∀ x, AEStronglyMeasurable (fun g => X.piU u' (γ⁻¹ * g * γ) x) (X.muH u) := by
    intro x
    have hc : ContinuousOn (fun g => X.piU u' (γ⁻¹ * g * γ) x) ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) :=
      ((X.piU_rep u').2.2.2.2 x).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
        (fun g hg => (hS g (hSH g hg)).1)
    have hm := hc.aestronglyMeasurable (μ := X.muH u) (isClosed_Hinf u).measurableSet
    have hae : ∀ᵐ g ∂(X.muH u), g ∈ ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := by
      rw [ae_iff]; exact (X.muH_haar u).2.2.1
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm
  have hW' : ∀ s ∈ X.SinfU u, ∀ x, X.Wu u' (γ⁻¹ * (s * x)) =
      X.psiInfU u s • X.piU u' (γ⁻¹ * s * γ) (X.Wu u' (γ⁻¹ * x)) := by
    intro s hs x
    rw [show γ⁻¹ * (s * x) = γ⁻¹ * s * γ * (γ⁻¹ * x) by group, (X.Wu_spec u').1 _ (hS s hs).1]
    exact congrArg (fun c : ℂ => c • X.piU u' (γ⁻¹ * s * γ) (X.Wu u' (γ⁻¹ * x))) (hS s hs).2
  have e1 : OOt t = ∫ x in FundOf t, (innerSL ℂ (X.Wu u' (γ⁻¹ * x))).smulRight (X.Wu u x)
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := rfl
  rw [e1]
  exact cross_zero (Formalism.L2.SG.ProjRows.muInf X.B.I) (X.muN u) (X.muH u) (X.nuQ u) (X.SinfU u) (X.NinfU u)
    ((Hinf X u : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) (ROinf t) (FundOf t) (X.piU u)
    (fun s => X.piU u' (γ⁻¹ * s * γ)) (X.psiInfU u) (X.Wu u) (fun x => X.Wu u' (γ⁻¹ * x))
    (X.nuQ_weil u) (fun s hs v => (hs v).1) hSH (fun n hn h hh => nh_mem u n h hn hh)
    (X.piU_rep u).2.1 (X.piU_rep u).2.2.2.1
    (fun a ha b hb => by
      show X.piU u' (γ⁻¹ * (a * b) * γ) = X.piU u' (γ⁻¹ * a * γ) * X.piU u' (γ⁻¹ * b * γ)
      rw [show γ⁻¹ * (a * b) * γ = (γ⁻¹ * a * γ) * (γ⁻¹ * b * γ) by group]
      exact (X.piU_rep u').2.1 _ (hS a ha).1 _ (hS b hb).1)
    (fun n hn => (X.piU_rep u').2.2.2.1 _ (hN n hn))
    (fun g hg => (X.piU_rep u).2.2.1 g (hSH g hg))
    (fun g hg => (X.piU_rep u').2.2.1 _ (hS g (hSH g hg)).1)
    (fun s _ => norm_psiInfU u s) (X.Wu_spec u).1
    (fun s hs x => hW' s hs x) (X.Wu_spec u).2.2.1
    ((X.Wu_spec u').2.2.1.comp (continuous_const.mul continuous_id))
    (X.muN_haar u).2.2.1 (X.muH_haar u).2.2.1 (fun g hg => (X.muH_haar u).2.2.2 g hg)
    (piU_aesm u) hσs hne hRc hRm hRi (fun a ha => (X.muN_haar u).2.2.2 a (hRN ha)) hΩ hOI

theorem idOffBlocks_of (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    (hFE : FundExists X u u' F0 F0' what₂ rows') (hOI : OOIntAll X u u' F0 F0' what₂ rows')
    (hHf : X.muH u Set.univ ≠ ⊤) (hC : IdOffConj F0 F0' what₂ rows' (X := X))
    (hI : IdOffIneq F0 F0' what₂ rows' (X := X)) (hR : IdOffRO F0 F0' what₂ rows' (X := X)) :
    IdOffBlocks F0 F0' cs cs' FdN FdN' := by
  intro hu ρ ρ'
  have hz : (fun t : {t : GTerm X u u' F0 F0' what₂ rows' // t.isId} => blk cs cs' FdN FdN' t.1 ρ ρ') =
      fun _ => 0 := by
    funext t
    have hΩ : IsSFund X.B.I (ROinf t.1) (FundOf t.1) := by
      have h := hFE t.1
      unfold FundOf
      rw [dif_pos h]
      exact h.choose_spec
    obtain ⟨hS, hN⟩ := hC hu t.1 t.2
    obtain ⟨hRc, hRm, hRi, hRN⟩ := hR hu t.1 t.2
    have h0 := oot_off_eq_zero t.1 hΩ (hOI t.1) hHf hS hN (hI hu t.1 t.2) hRc hRm hRi hRN
    unfold blk
    split_ifs
    · rw [h0, smul_zero, smul_zero]
    · rfl
  rw [hz]
  exact hasSum_zero

end Off

section ClosedOff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def IdOffC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    IdOffConj (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) ∧
      IdOffIneq (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X) ∧
      IdOffRO (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)

theorem idCellOffC_of_steps (hV : VolPosC) (hS : IdOffC) : IdCellOffC :=
  idCellOffC_of fun D X Y u u' hFE hOI => by
    obtain ⟨_, hH⟩ := hV D X Y u (Formalism.L2.SG.Closed.level_subgroup_properties X)
    obtain ⟨hC, hI, hR⟩ := hS D X Y u u' hFE
    exact idOffBlocks_of (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hFE hOI
      (ENNReal.toReal_pos_iff.1 hH).2.ne hC hI hR

end ClosedOff

end Formalism.L2.SG.TermOp.IdBlocks
