import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainTheta

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.UniformTranslateBound

open Filter Topology
open scoped Classical

theorem schwartz_translate_decay {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) (k : ℕ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : E, ‖y‖ ≤ R → ‖f (x + y)‖ ≤ D * ((1 + ‖x‖) ^ k)⁻¹ := by
  set M := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f with hM
  have h0 : ∀ w : E, (1 + ‖w‖) ^ k * ‖f w‖ ≤ M := fun w => by
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f w
    rwa [norm_iteratedFDeriv_zero] at h1
  have hM0 : 0 ≤ M := le_trans (by positivity) (h0 0)
  refine ⟨(1 + R) ^ k * M, by positivity, fun x y hy => ?_⟩
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  have h2 : 1 + ‖x‖ ≤ (1 + R) * (1 + ‖x + y‖) := by
    have : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by simpa using norm_sub_le (x + y) y
    nlinarith [norm_nonneg (x + y), norm_nonneg y, mul_nonneg hR (norm_nonneg (x + y))]
  calc ‖f (x + y)‖ * (1 + ‖x‖) ^ k ≤ ‖f (x + y)‖ * ((1 + R) * (1 + ‖x + y‖)) ^ k := by gcongr
    _ = (1 + R) ^ k * ((1 + ‖x + y‖) ^ k * ‖f (x + y)‖) := by rw [mul_pow]; ring
    _ ≤ (1 + R) ^ k * M := by gcongr; exact h0 _

theorem summable_one_add_norm_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖(z : E)‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
  gcongr
  show ‖z‖ ≤ 1 + ‖z‖
  linarith

variable (F : Type) [Field F] [NumberField F]

theorem mixed_algebraMap_fst (x : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AdeleRing (𝓞 F) F) x).1 = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem pureA_bound {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  let zi : (κ → AdeleRing (𝓞 F) F) → (κ → mixedEmbedding.mixedSpace F) :=
    fun z i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
  let zf : (κ → AdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun z i => (z i).2
  have hzi : Continuous zi :=
    continuous_pi fun i => (GlobalTheory.ThetaTransformMeas.continuous_mixed F).comp (continuous_fst.comp (continuous_apply i))
  have hzf : Continuous zf := continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  obtain ⟨R, hR⟩ := (hK.image hzi).isBounded.subset_closedBall 0
  obtain ⟨Bg, hBg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hBg0 : 0 ≤ Bg := (norm_nonneg _).trans (hBg 0)
  let C : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun p => p.1 - p.2) '' (tsupport g ×ˢ (zf '' K))
  have hC : IsCompact C := (hg.2.isCompact.prod (hK.image hzf)).image (continuous_fst.sub continuous_snd)
  obtain ⟨N, hN, hNC⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hC
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let e : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i)
  let S : Set (κ → F) := {ξ | e ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  obtain ⟨D, hD0, hD⟩ := schwartz_translate_decay f (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1)
    (max R 0) (le_max_right _ _)
  let h : (κ → F) → ℝ := S.indicator fun ξ =>
    D * ((1 + ‖e ξ‖) ^ (Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1))⁻¹ * Bg
  have hh : ∀ ξ, 0 ≤ h ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
  have hsum : Summable h := by
    rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b hab => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val hab) i))
    exact (((summable_one_add_norm_inv _).comp_injective hj).mul_left D).mul_right Bg
  refine ⟨∑' ξ, h ξ, fun z hz s => ?_⟩
  refine le_trans (Finset.sum_le_sum fun ξ _ => ?_) (hsum.sum_le_tsum s fun ξ _ => hh ξ)
  have hsplit : GlobalTheory.WeilM.pureA F f g ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z) =
      f (e ξ + zi z) * g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) := by
    unfold GlobalTheory.WeilM.pureA
    congr 2
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((algebraMap F (AdeleRing (𝓞 F) F) (ξ i)).1 + (z i).1) = _
    rw [map_add, mixed_algebraMap_fst]
    rfl
  rw [hsplit, norm_mul]
  by_cases hg0 : g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + zf z) = 0
  · rw [hg0, norm_zero, mul_zero]; exact hh ξ
  have hmem : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ C :=
    ⟨(_, zf z), ⟨subset_tsupport _ hg0, z, hz, rfl⟩, add_sub_cancel_right _ _⟩
  have hξS : ξ ∈ S := by
    show ∀ i, (N : ℝ) • e ξ i ∈ mixedEmbedding.integerLattice F
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hNC _ hmem i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  show _ ≤ S.indicator _ ξ
  rw [Set.indicator_of_mem hξS]
  have hzR : ‖zi z‖ ≤ max R 0 := le_max_of_le_left (mem_closedBall_zero_iff.1 (hR ⟨z, hz, rfl⟩))
  exact mul_le_mul (hD _ _ hzR) (hBg _) (norm_nonneg _) (by positivity)

theorem schA_bound_compact {κ : Type} [Fintype κ] {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ)
    {K : Set (κ → AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ s : Finset (κ → F),
      ∑ ξ ∈ s, ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + z)‖ ≤ B := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact pureA_bound F f hg hK
  | zero => exact ⟨0, fun z _ s => by simp⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨B1, hB1⟩ := h1
    obtain ⟨B2, hB2⟩ := h2
    refine ⟨B1 + B2, fun z hz s => ?_⟩
    refine le_trans (Finset.sum_le_sum fun ξ _ => norm_add_le (Φ _) (Ψ _)) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add (hB1 z hz s) (hB2 z hz s)
  | smul c Φ _ h =>
    obtain ⟨B, hB⟩ := h
    refine ⟨‖c‖ * B, fun z hz s => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hB z hz s) (norm_nonneg c)

theorem tsum_norm_translate_le : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι],
    ∀ Φ ∈ GlobalTheory.WeilM.schA F ι,
    ∃ B : ℝ, ∀ z : ι → AF F, ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ ≤ B := by
  intro F _ _ ι _ Φ hΦ
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.RatVecDomain.exists_compact_cover_ratVec F ι
  obtain ⟨B, hB⟩ := schA_bound_compact F hΦ hK
  refine ⟨B, fun z => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hcov z
  obtain ⟨η, rfl⟩ := (GlobalTheory.ThetaParseval.mem_ratVec_iff _).1 hγ
  let G : (ι → F) → ℝ := fun ξ =>
    ‖Φ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) + ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (η i)) + z))‖
  have hG : ∀ ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = G (Equiv.subRight η ξ) := by
    intro ξ
    show _ = ‖Φ _‖
    congr 2
    funext i
    simp only [Equiv.subRight_apply, Pi.add_apply, Pi.sub_apply, map_sub]
    abel
  calc ∑' ξ : ι → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + z)‖ = ∑' ξ, G (Equiv.subRight η ξ) := tsum_congr hG
    _ = ∑' ξ, G ξ := (Equiv.subRight η).tsum_eq G
    _ ≤ B := Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) (hB _ hγK)

end GlobalTheory.UniformTranslateBound
