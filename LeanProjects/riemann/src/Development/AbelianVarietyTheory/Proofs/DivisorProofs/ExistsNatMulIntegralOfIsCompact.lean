import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples

noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
private lemma natCast_mul_mem_adicCompletionIntegers (N : ℕ) {b : FiniteAdeleRing (𝓞 F) F}
    {v : HeightOneSpectrum (𝓞 F)} (hb : b v ∈ HeightOneSpectrum.adicCompletionIntegers F v) :
    ((N : FiniteAdeleRing (𝓞 F) F) * b) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  rw [← nsmul_eq_mul]
  exact nsmul_mem hb N

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact {κ : Type} [Fintype κ]
    {K : Set (κ → FiniteAdeleRing (𝓞 F) F)}
    (hK : IsCompact K) : ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, ∀ i v,
      ((N : FiniteAdeleRing (𝓞 F) F) * x i) v ∈ HeightOneSpectrum.adicCompletionIntegers F v := by
  have hW : IsOpen {a : FiniteAdeleRing (𝓞 F) F |
      ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hopen : ∀ m : ℕ, IsOpen {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
      (((m + 1 : ℕ) : FiniteAdeleRing (𝓞 F) F) * x i) v ∈
        HeightOneSpectrum.adicCompletionIntegers F v} := by
    intro m
    have hopen' : IsOpen (⋂ i : κ, (fun x : κ → FiniteAdeleRing (𝓞 F) F =>
        ((m + 1 : ℕ) : FiniteAdeleRing (𝓞 F) F) * x i) ⁻¹'
          {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}) :=
      isOpen_iInter_of_finite fun i => hW.preimage (continuous_const.mul (continuous_apply i))
    simpa only [Set.preimage_setOf_eq, Set.iInter_setOf] using hopen'
  have hcover : K ⊆ ⋃ m : ℕ, {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ i v,
      (((m + 1 : ℕ) : FiniteAdeleRing (𝓞 F) F) * x i) v ∈
        HeightOneSpectrum.adicCompletionIntegers F v} := by
    intro x _
    choose M hM hMx using fun i => _root_.GlobalTheory.IntegralFinAdele.exists_nat_mul_integral F (x i)
    refine Set.mem_iUnion.mpr ⟨(∏ i, M i) - 1, fun i v => ?_⟩
    have hpos : 0 < ∏ i, M i := Finset.prod_pos fun i _ => hM i
    rw [Nat.sub_add_cancel hpos]
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem M (Finset.mem_univ i)
    rw [he, Nat.cast_mul, mul_comm ((M i : ℕ) : FiniteAdeleRing (𝓞 F) F), mul_assoc]
    exact natCast_mul_mem_adicCompletionIntegers F e (hMx i v)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ hopen hcover
  · refine ⟨∏ m ∈ t, (m + 1), Finset.prod_pos fun m _ => m.succ_pos, fun x hx i v => ?_⟩
    obtain ⟨m, hm, hxm⟩ := Set.mem_iUnion₂.mp (ht hx)
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun m : ℕ => m + 1) hm
    rw [he, Nat.cast_mul, mul_comm ((((m + 1 : ℕ)) : FiniteAdeleRing (𝓞 F) F)), mul_assoc]
    exact natCast_mul_mem_adicCompletionIntegers F e (hxm i v)

def denomLattice (κ : Type) (N : ℕ) : Submodule ℤ (κ → mixedEmbedding.mixedSpace F) where
  carrier := {x | ∀ i, (N : ℝ) • x i ∈ mixedEmbedding.integerLattice F}
  zero_mem' := fun i => by simp
  add_mem' := fun ha hb i => by
    rw [Pi.add_apply, smul_add]; exact add_mem (ha i) (hb i)
  smul_mem' := fun c x hx i => by
    rw [Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ c (hx i)

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.WeilM.discreteTopology_denomLattice (κ : Type) [Fintype κ] {N : ℕ} (hN : 0 < N) :
    DiscreteTopology (_root_.GlobalTheory.WeilM.denomLattice F κ N) := by
  let ψ : _root_.GlobalTheory.WeilM.denomLattice F κ N → (κ → mixedEmbedding.integerLattice F) :=
    fun z i => ⟨(N : ℝ) • (z : κ → mixedEmbedding.mixedSpace F) i, z.2 i⟩
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  refine DiscreteTopology.of_continuous_injective (f := ψ) ?_ ?_
  · refine continuous_pi fun i => ?_
    show Continuous fun z : _root_.GlobalTheory.WeilM.denomLattice F κ N =>
      (⟨(N : ℝ) • (z : κ → mixedEmbedding.mixedSpace F) i, z.2 i⟩ : mixedEmbedding.integerLattice F)
    exact Continuous.subtype_mk ((continuous_const (y := (N : ℝ))).smul
      ((continuous_apply (A := fun _ : κ => mixedEmbedding.mixedSpace F) i).comp
        continuous_subtype_val)) _
  · intro z w hzw
    refine Subtype.ext (funext fun i => smul_right_injective _ hN' ?_)
    exact congrArg (fun p => ((p i : mixedEmbedding.integerLattice F) :
      mixedEmbedding.mixedSpace F)) hzw

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.WeilM.pureA_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) :
    _root_.GlobalTheory.WeilM.pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) =
      f (fun i => mixedEmbedding F (ξ i)) *
        g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := by
  unfold _root_.GlobalTheory.WeilM.pureA
  congr 2
  funext i
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · simp [mixedEmbedding.mixedEmbedding_apply_isReal]
  · simp [mixedEmbedding.mixedEmbedding_apply_isComplex]

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
private lemma summable_norm_schwartz_on_discrete_lattice {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) : Summable fun z : L => ‖f z‖ := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = Module.finrank ℤ L + 1 := ⟨_, rfl⟩
  have hr : -(k : ℝ) < -(Module.finrank ℤ L : ℝ) := by
    rw [hk]; push_cast; linarith
  refine Summable.of_norm_bounded_eventually
    ((ZLattice.summable_norm_rpow L (-(k : ℝ)) hr).mul_left (SchwartzMap.seminorm ℝ k 0 f)) ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with z hz
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hle := SchwartzMap.le_seminorm ℝ k 0 f (z : E)
  rw [norm_iteratedFDeriv_zero] at hle
  rw [norm_norm, Real.rpow_neg hz'.le, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (pow_pos hz' k), mul_comm]
  exact hle

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
private lemma mem_integers_of_forall_integral_finiteAdele (x : F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v ∈
      HeightOneSpectrum.adicCompletionIntegers F v) : x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  have hv := h v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation] using hv

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.WeilM.summable_pureA {κ : Type} [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ _root_.GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    Summable fun ξ : κ → F =>
      _root_.GlobalTheory.WeilM.pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  obtain ⟨hloc, hcpt⟩ := hg'
  obtain ⟨B, hB⟩ := hcpt.exists_bound_of_continuous hloc.continuous
  obtain ⟨N, hN, hNK⟩ := _root_.GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F (K := tsupport g) hcpt
  haveI := _root_.GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  have hL : Summable (((_root_.GlobalTheory.WeilM.denomLattice F κ N : Submodule ℤ _) :
      Set (κ → mixedEmbedding.mixedSpace F)).indicator fun z => ‖f z‖) :=
    summable_subtype_iff_indicator.mp
      (summable_norm_schwartz_on_discrete_lattice (_root_.GlobalTheory.WeilM.denomLattice F κ N) f)
  have hinj : Function.Injective fun ξ : κ → F => fun i => mixedEmbedding F (ξ i) :=
    fun ξ η h => funext fun i => mixedEmbedding_injective F (congrFun h i)
  refine Summable.of_norm_bounded_eventually ((hL.comp_injective hinj).mul_left B)
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [_root_.GlobalTheory.WeilM.pureA_algebraMap, norm_mul, Function.comp_apply]
  by_cases hξ : g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = 0
  · rw [hξ, norm_zero, mul_zero]
    exact mul_nonneg ((norm_nonneg _).trans (hB 0))
      (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  · have hmem : (fun i => mixedEmbedding F (ξ i)) ∈ _root_.GlobalTheory.WeilM.denomLattice F κ N := by
      show ∀ i, (N : ℝ) • mixedEmbedding F (ξ i) ∈ mixedEmbedding.integerLattice F
      intro i
      have hint : ∀ v, (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N * ξ i)) v ∈
          HeightOneSpectrum.adicCompletionIntegers F v := by
        intro v
        have h := hNK _ (subset_tsupport g hξ) i v
        rwa [show (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) =
          algebraMap F (FiniteAdeleRing (𝓞 F) F) (N * ξ i) by simp] at h
      obtain ⟨y, hy⟩ := mem_integers_of_forall_integral_finiteAdele F _ hint
      rw [Nat.cast_smul_eq_nsmul ℝ, ← map_nsmul, nsmul_eq_mul, ← hy]
      exact ⟨y, rfl⟩
    rw [Set.indicator_of_mem hmem, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.WeilM.summable_of_mem_schA {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ _root_.GlobalTheory.WeilM.schA F κ) :
    Summable fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
  unfold _root_.GlobalTheory.WeilM.schA at hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact _root_.GlobalTheory.WeilM.summable_pureA F f hg
  | zero => simpa using (summable_zero : Summable fun _ : κ → F => (0 : ℂ))
  | add x y _ _ hx hy => simpa only [Pi.add_apply] using hx.add hy
  | smul a x _ hx => simpa only [Pi.smul_apply, smul_eq_mul] using hx.mul_left a

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.WeilM.summable_norm_of_mem_schA {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ _root_.GlobalTheory.WeilM.schA F κ) :
    Summable fun ξ : κ → F => ‖Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
  summable_norm_iff.mpr (_root_.GlobalTheory.WeilM.summable_of_mem_schA F hΦ)

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.WeilM.hasSum_thetaSum {κ : Type} [Fintype κ]
    {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ _root_.GlobalTheory.WeilM.schA F κ) :
    HasSum (fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))
      (_root_.GlobalTheory.WeilM.thetaSum F Φ) := by
  unfold _root_.GlobalTheory.WeilM.thetaSum
  exact (_root_.GlobalTheory.WeilM.summable_of_mem_schA F hΦ).hasSum

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.WeilM.thetaSum_add {κ : Type} [Fintype κ]
    {Φ Ψ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ _root_.GlobalTheory.WeilM.schA F κ)
    (hΨ : Ψ ∈ _root_.GlobalTheory.WeilM.schA F κ) :
    _root_.GlobalTheory.WeilM.thetaSum F (Φ + Ψ) =
      _root_.GlobalTheory.WeilM.thetaSum F Φ + _root_.GlobalTheory.WeilM.thetaSum F Ψ := by
  unfold _root_.GlobalTheory.WeilM.thetaSum
  simp only [Pi.add_apply]
  exact (_root_.GlobalTheory.WeilM.summable_of_mem_schA F hΦ).tsum_add
    (_root_.GlobalTheory.WeilM.summable_of_mem_schA F hΨ)

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.WeilM.thetaSum_smul {κ : Type} (c : ℂ) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    _root_.GlobalTheory.WeilM.thetaSum F (c • Φ) = c * _root_.GlobalTheory.WeilM.thetaSum F Φ := by
  unfold _root_.GlobalTheory.WeilM.thetaSum
  simp only [Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

def thetaLin (κ : Type) [Fintype κ] : schA F κ →ₗ[ℂ] ℂ where
  toFun Φ := thetaSum F Φ.1
  map_add' Φ Ψ := thetaSum_add F Φ.2 Ψ.2
  map_smul' c Φ := thetaSum_smul F c Φ.1

@[simp] theorem thetaLin_apply {κ : Type} [Fintype κ] (Φ : schA F κ) : thetaLin F κ Φ = thetaSum F Φ.1 := rfl

open NumberField IsDedekindDomain in
open scoped Classical in
variable (F : Type) [Field F] [NumberField F] in

theorem _root_.GlobalTheory.WeilM.thetaSum_summable_linear (κ : Type) [Fintype κ] :
    (∀ Φ ∈ _root_.GlobalTheory.WeilM.schA F κ,
      Summable fun ξ : κ → F => Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ∧
    (∀ Φ ∈ _root_.GlobalTheory.WeilM.schA F κ,
      Summable fun ξ : κ → F => ‖Φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖) ∧
    (∀ Φ ∈ _root_.GlobalTheory.WeilM.schA F κ, ∀ Ψ ∈ _root_.GlobalTheory.WeilM.schA F κ,
      _root_.GlobalTheory.WeilM.thetaSum F (Φ + Ψ) =
        _root_.GlobalTheory.WeilM.thetaSum F Φ + _root_.GlobalTheory.WeilM.thetaSum F Ψ) ∧
    (∀ (c : ℂ), ∀ Φ ∈ _root_.GlobalTheory.WeilM.schA F κ,
      _root_.GlobalTheory.WeilM.thetaSum F (c • Φ) = c * _root_.GlobalTheory.WeilM.thetaSum F Φ) :=
  ⟨fun _ hΦ => _root_.GlobalTheory.WeilM.summable_of_mem_schA F hΦ,
    fun _ hΦ => _root_.GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦ,
    fun _ hΦ _ hΨ => _root_.GlobalTheory.WeilM.thetaSum_add F hΦ hΨ,
    fun c Φ _ => _root_.GlobalTheory.WeilM.thetaSum_smul F c Φ⟩

end GlobalTheory.WeilM
