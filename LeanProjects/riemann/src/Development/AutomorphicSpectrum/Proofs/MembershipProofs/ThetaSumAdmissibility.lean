import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.GlobalFields.Adele.Compact

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct SchwartzMap nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaAdm

theorem tempered_sum {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : X → E) (w : X → ℂ) (k : ℕ)
    (h : Summable fun x => ‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹) :
    (∀ f : 𝓢(E, ℂ), Summable fun x => ‖f (p x) * w x‖) ∧
      ∃ T : 𝓢(E, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(E, ℂ), T f = ∑' x, f (p x) * w x := by
  have hb : ∀ (f : 𝓢(E, ℂ)) (x : X), ‖f (p x) * w x‖ ≤
      (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) * (‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹) := by
    intro f x
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f (p x)
    rw [norm_iteratedFDeriv_zero] at h1
    have hp : 0 < (1 + ‖p x‖) ^ k := by positivity
    have h2 : ‖f (p x)‖ ≤ (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) *
        ((1 + ‖p x‖) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact h1
    rw [norm_mul]
    calc _ ≤ (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) * ((1 + ‖p x‖) ^ k)⁻¹ * ‖w x‖ := by
          gcongr
      _ = _ := by ring
  have hs : ∀ f : 𝓢(E, ℂ), Summable fun x => ‖f (p x) * w x‖ := fun f =>
    (h.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) (hb f)
  refine ⟨hs, SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => ∑' x, f (p x) * w x) ?_ ?_ ?_, fun f => rfl⟩
  · intro f g
    rw [← (hs f).of_norm.tsum_add (hs g).of_norm]
    simp [add_mul]
  · intro a f
    simp [← tsum_mul_left, mul_assoc]
  · refine ⟨Finset.Iic (k, 0), 2 ^ k * ∑' x, ‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹,
      mul_nonneg (by positivity) (tsum_nonneg fun x => by positivity), fun f => ?_⟩
    refine (tsum_of_norm_bounded (h.mul_left _).hasSum (hb f)).trans_eq ?_
    rw [tsum_mul_left]
    ring

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix in

theorem summable_weight {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ k : ℕ, Summable fun x : κ → F => ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i))‖ *
      ((1 + ‖(fun i => mixedEmbedding F (x i) : κ → mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹ := by
  obtain ⟨hlc, hc⟩ := hg
  obtain ⟨C, hC⟩ := hlc.continuous.bounded_above_of_compact_support hc
  have hS : IsCompact (⋃ i : κ, (fun y : κ → FiniteAdeleRing (𝓞 F) F => y i) '' tsupport g) :=
    isCompact_iUnion fun i => hc.isCompact.image (continuous_apply i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F d)⁻¹)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hdK))
  let I : κ → (FractionalIdeal (𝓞 F)⁰ F)ˣ := fun _ => J
  set k := Module.finrank ℤ (idealLatticePi I) + 1
  refine ⟨k, ?_⟩
  have h1 : Summable fun α : idealLatticePi I => ((1 + ‖α‖) ^ k)⁻¹ := by
    have hs := ZLattice.summable_norm_pow_inv (L := idealLatticePi I) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : idealLatticePi I)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  have h2 := (summable_norm_iff_and_tsum_eq_cosetPi I 0 (fun v => ((((1 + ‖v‖) ^ k)⁻¹ : ℝ) : ℂ))).1.mpr (by
    refine h1.congr fun α => ?_
    rw [embPi_zero, add_zero, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rfl)
  refine (h2.mul_left C).of_nonneg_of_le (fun x => by positivity) fun x => ?_
  by_cases hx : g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i)) = 0
  · rw [hx, norm_zero, zero_mul]
    exact mul_nonneg ((norm_nonneg _).trans (hC 0)) (norm_nonneg _)
  · have hmem : x ∈ cosetPi F I 0 := by
      intro i
      have h3 := hd _ (Set.mem_iUnion.mpr ⟨i, _, subset_tsupport g hx, rfl⟩)
      rw [← map_mul] at h3
      obtain ⟨z, hz⟩ := exists_eq_of_forall_mem_adicCompletionIntegers F _ h3
      refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨z, ?_⟩
      rw [Algebra.smul_def, show algebraMap (𝓞 F) F z = _ from hz]
      simp only [Pi.zero_apply, sub_zero]
      field_simp
    rw [Set.indicator_of_mem hmem, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hC _) (by positivity)

omit [Fintype κ] in

theorem pureA_rat (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → F) :
    pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i)) =
      f (fun i => mixedEmbedding F (x i)) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i)) := by
  simp only [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem summable_schA {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Summable fun x : κ → F => ‖Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i))‖ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨k, hk⟩ := summable_weight F hg
    simpa only [pureA_rat] using (tempered_sum _ _ k hk).1 f
  | zero => simp
  | add Φ Ψ _ _ h1 h2 => exact (h1.add h2).of_nonneg_of_le (fun _ => norm_nonneg _) fun x => norm_add_le _ _
  | smul a Φ _ h => simpa [norm_mul] using h.mul_left ‖a‖

def thetaLin : schA F κ →ₗ[ℂ] ℂ where
  toFun Φ := thetaSum F Φ.1
  map_add' Φ Ψ := (summable_schA F Φ.2).of_norm.tsum_add (summable_schA F Ψ.2).of_norm
  map_smul' a Φ := by simp [thetaSum, tsum_mul_left]

open GroundTheory.Global in

theorem indicator_mem_SB : (Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator
    (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have hc : IsCompact (Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    isCompact_univ_pi fun _ => isCompact_integralFiniteAdeles F
  have ho : IsOpen (Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integralFiniteAdeles
  have hcl : IsClosed (Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))) :=
    isClosed_set_pi fun _ _ =>
      AddSubgroup.isClosed_of_isOpen (integralFiniteAdeles (𝓞 F) F).toAddSubgroup isOpen_integralFiniteAdeles
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))
  · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
  · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩

open GroundTheory.Global in

theorem exists_thetaSum_ne_zero : ∃ Φ ∈ schA F κ, thetaSum F Φ ≠ 0 := by
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := default
  have hb : HasCompactSupport fun v => (b v : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) fun v => (b v : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let f : 𝓢(κ → mixedEmbedding.mixedSpace F, ℂ) := hb.toSchwartzMap hb'
  have hf : ∀ v, f v = (b v : ℂ) := fun _ => rfl
  set O := Set.univ.pi fun _ : κ => (integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hO
  have hm : pureA F f (O.indicator fun _ => (1 : ℂ)) ∈ schA F κ :=
    Submodule.subset_span ⟨f, _, indicator_mem_SB F, rfl⟩
  refine ⟨_, hm, ?_⟩
  have hn : ∀ x : κ → F, pureA F f (O.indicator fun _ => (1 : ℂ)) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i)) =
      ((‖pureA F f (O.indicator fun _ => (1 : ℂ)) (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i))‖ : ℝ) : ℂ) := by
    intro x
    rw [pureA_rat, hf]
    by_cases hx : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i)) ∈ O
    · rw [Set.indicator_of_mem hx, mul_one, Complex.norm_real, Real.norm_of_nonneg b.nonneg]
    · simp [Set.indicator_of_notMem hx]
  rw [thetaSum, tsum_congr hn, ← Complex.ofReal_tsum, Complex.ofReal_ne_zero]
  refine ((summable_schA F hm).tsum_pos (fun _ => norm_nonneg _) 0 ?_).ne'
  have h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈ O := fun i _ => by
    show algebraMap F (FiniteAdeleRing (𝓞 F) F) 0 ∈ integralFiniteAdeles (𝓞 F) F
    rw [map_zero]
    exact Subring.zero_mem _
  have h1 : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := funext fun i => map_zero _
  rw [pureA_rat, hf, Set.indicator_of_mem h0, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  simp

theorem theta_adm : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ],
    (∀ Φ ∈ schA F κ, Summable fun x : κ → F => ‖Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (x i))‖) ∧
    (∃ l ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ) ∧ ∃ Φ ∈ schA F κ, thetaSum F Φ ≠ 0 := by
  intro F _ _ _ _ κ _
  refine ⟨fun Φ hΦ => summable_schA F hΦ, ?_, exists_thetaSum_ne_zero F⟩
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F (κ := κ))
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, fun g hg => ?_, hl'⟩
  obtain ⟨k, hk⟩ := summable_weight F hg
  obtain ⟨T, hT⟩ := (tempered_sum _ _ k hk).2
  refine ⟨T, fun f => ?_⟩
  rw [hT, hl' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), thetaSum]
  simp only [pureA_rat]

end GlobalTheory.CompanionTheory.ThetaAdm
