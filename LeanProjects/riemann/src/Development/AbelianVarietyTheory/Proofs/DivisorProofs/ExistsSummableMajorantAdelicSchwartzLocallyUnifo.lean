import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.SchwartzMajorant

variable (F : Type) [Field F] [NumberField F]

theorem pureA_add_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j) =
      f ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1) *
      g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j => (x j).2) := by
  unfold GlobalTheory.WeilM.pureA
  congr 2
  funext j
  simp only [Pi.add_apply]
  rw [show (algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j).1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ j)).1 + (x j).1 from rfl,
    map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem norm_le_of_decay {V : Type} [NormedAddCommGroup V] {φ : V → ℂ} {k : ℕ} {C0 Ck : ℝ}
    (h0 : ∀ v, ‖φ v‖ ≤ C0) (hk : ∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) (w a : V) :
    ‖φ (w + a)‖ * (1 + ‖w‖) ^ k ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k := by
  set u := w + a with hu
  have hCk : 0 ≤ Ck := le_trans (by positivity) (hk 0)
  have hC0 : 0 ≤ C0 := le_trans (norm_nonneg _) (h0 0)
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have h1 : ‖φ u‖ * (1 + ‖u‖) ^ k ≤ 2 ^ k * (C0 + Ck) := by
    rcases le_total ‖u‖ 1 with hu1 | hu1
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ C0 * 2 ^ k :=
            mul_le_mul (h0 u) (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity) hC0
        _ ≤ _ := by nlinarith
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ ‖φ u‖ * (2 * ‖u‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = 2 ^ k * (‖u‖ ^ k * ‖φ u‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ k * Ck := mul_le_mul_of_nonneg_left (hk u) h2k.le
        _ ≤ _ := by nlinarith
  have h2 : (1 + ‖w‖) ^ k ≤ (1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ‖w‖ ≤ ‖u‖ + ‖a‖ := by
      calc ‖w‖ = ‖u - a‖ := by rw [hu, add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg u, norm_nonneg a]
  calc ‖φ u‖ * (1 + ‖w‖) ^ k ≤ ‖φ u‖ * ((1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (‖φ u‖ * (1 + ‖u‖) ^ k) * (1 + ‖a‖) ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem summable_one_add_norm_pow_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

theorem exists_majorant_pureA {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (x : κ → AdeleRing (𝓞 F) F) :
    ∃ k : ℕ, ∃ M : (κ → F) → ℝ, Summable M ∧ ∀ (C0 Ck : ℝ) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
      (∀ v, ‖φ v‖ ≤ C0) → (∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) → ∀ ξ : κ → F,
        ‖GlobalTheory.WeilM.pureA F φ g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ (C0 + Ck) * M ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  let xf : κ → FiniteAdeleRing (𝓞 F) F := fun j => (x j).2
  let a : κ → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  have hK : IsCompact ((fun y => y - xf) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ j => mixedEmbedding F (ξ j)
  let S : Set (κ → F) := {ξ | v ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  let k := Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1
  refine ⟨k, S.indicator fun ξ => 2 ^ k * (1 + ‖a‖) ^ k * B * ((1 + ‖v ξ‖) ^ k)⁻¹, ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨v ξ, ξ.2⟩
    have hj : Function.Injective j := fun p q h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact ((summable_one_add_norm_pow_inv (GlobalTheory.WeilM.denomLattice F κ N)).comp_injective hj).mul_left _
  · intro C0 Ck φ h0 hk ξ
    rw [pureA_add_algebraMap, norm_mul]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hd := norm_le_of_decay h0 hk (v ξ) a
      have hpos : 0 < (1 + ‖v ξ‖) ^ k := by positivity
      have h1 : ‖φ (v ξ + a)‖ ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hd
      calc ‖φ (v ξ + a)‖ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖
          ≤ (2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have hz : g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf) = 0 := by
        by_contra h0'
        apply hξ
        have hmem : (fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) ∈ (fun y => y - xf) '' tsupport g :=
          ⟨_, subset_tsupport _ h0', add_sub_cancel_right _ _⟩
        show ∀ i, (N : ℝ) • v ξ i ∈ mixedEmbedding.integerLattice F
        intro i
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun w => by
          rw [map_mul, map_natCast]
          exact hKN _ hmem i w
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      show _ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖ ≤ 0
      rw [hz, norm_zero, mul_zero]

theorem exists_summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type}
    [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  intro F _ _ κ _ P _ Ψ p0 m g f hg hΨ hC x
  choose k M hM hbound using fun i => exists_majorant_pureA F (hg i) x
  choose C hCev using hC
  refine ⟨fun ξ => ∑ i, (C 0 + C (k i)) * M i ξ, summable_sum fun i _ => (hM i).mul_left _, ?_⟩
  have hall : ∀ᶠ p in nhds p0, ∀ i, (∀ v, ‖v‖ ^ 0 * ‖f p i v‖ ≤ C 0) ∧
      (∀ v, ‖v‖ ^ k i * ‖f p i v‖ ≤ C (k i)) :=
    Filter.eventually_all.2 fun i => ((hCev 0).and (hCev (k i))).mono fun p hp => ⟨hp.1 i, hp.2 i⟩
  filter_upwards [hΨ, hall] with p hp hb ξ
  rw [hp, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i _ _ _ (fun v => ?_) (hb i).2 ξ)
  simpa using (hb i).1 v

end GlobalTheory.SchwartzMajorant
