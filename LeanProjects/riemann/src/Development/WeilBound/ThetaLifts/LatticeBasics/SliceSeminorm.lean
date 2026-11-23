import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : Type} [Fintype κ]

variable (V κ) in

def dgL : (κ → V) →L[ℝ] (κ ⊕ κ → V) := GlobalTheory.SchwartzBox.restr V (Sum.elim id id)

theorem dg_add (x u : κ → V) : dgL V κ u + Sum.elim x 0 = Sum.elim (u + x) u := by
  funext i; cases i <;> simp [dgL, GlobalTheory.SchwartzBox.restr_apply]

theorem le_elim_r (x u : κ → V) : ‖u‖ ≤ ‖Sum.elim x u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (Sum.elim x u) (.inr i)

theorem le_elim_l (x u : κ → V) : ‖x‖ ≤ ‖Sum.elim x u‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (Sum.elim x u) (.inl i)

def slice (x : κ → V) : 𝓢(κ ⊕ κ → V, ℂ) →L[ℂ] 𝓢(κ → V, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun u => dgL V κ u + Sum.elim x 0)
    ((dgL V κ).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _))
    ⟨1, 1, fun u => by rw [dg_add]; have := le_elim_r (u + x) u; linarith⟩

theorem slice_apply (x : κ → V) (f : 𝓢(κ ⊕ κ → V, ℂ)) (u : κ → V) : slice x f u = f (Sum.elim (u + x) u) := by
  rw [← dg_add]; rfl

theorem slice_seminorm (f : 𝓢(κ ⊕ κ → V, ℂ)) (N k n : ℕ) (x : κ → V) :
    ‖x‖ ^ N * SchwartzMap.seminorm ℂ k n (slice x f) ≤ 2 ^ N * SchwartzMap.seminorm ℂ (N + k) n f := by
  have key : ∀ u, ‖x‖ ^ N * (‖u‖ ^ k * ‖iteratedFDeriv ℝ n (slice x f) u‖) ≤
      2 ^ N * SchwartzMap.seminorm ℂ (N + k) n f := fun u => by
    have e : ⇑(slice x f) = fun y => (SchwartzMap.compSubConstCLM ℂ (-Sum.elim x 0) f) (y ∘ Sum.elim id id) := by
      funext y; rw [slice_apply, ← dg_add]; simp [dgL, GlobalTheory.SchwartzBox.restr_apply]
    have h1 := GlobalTheory.SchwartzBox.norm_iteratedFDeriv_restr_le (Sum.elim id id)
      (SchwartzMap.compSubConstCLM ℂ (-Sum.elim x 0) f) n u
    have e2 : ⇑(SchwartzMap.compSubConstCLM ℂ (-Sum.elim x 0) f) = fun z => f (z + Sum.elim x 0) := by
      funext z; simp
    rw [← e, e2, iteratedFDeriv_comp_add_right, show u ∘ Sum.elim id id + Sum.elim x 0 = _ from dg_add x u] at h1
    set z := Sum.elim (u + x) u
    have hu : ‖u‖ ≤ ‖z‖ := le_elim_r _ _
    have hx : ‖x‖ ≤ 2 * ‖z‖ := by
      have := norm_sub_le (u + x) u
      have h : ‖u + x‖ ≤ ‖z‖ := le_elim_l _ _
      rw [add_sub_cancel_left] at this; linarith
    calc _ ≤ (2 * ‖z‖) ^ N * (‖z‖ ^ k * ‖iteratedFDeriv ℝ n f z‖) := by gcongr
      _ = 2 ^ N * (‖z‖ ^ (N + k) * ‖iteratedFDeriv ℝ n f z‖) := by ring
      _ ≤ _ := by gcongr; exact SchwartzMap.le_seminorm ℂ _ _ f z
  rcases (pow_nonneg (norm_nonneg x) N).eq_or_lt with h | h
  · rw [← h, zero_mul]; positivity
  · rw [mul_comm, ← le_div_iff₀ h]
    exact SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun u => by rw [le_div_iff₀ h, mul_comm]; exact key u

theorem slice_bound (T : 𝓢(κ → V, ℂ) →L[ℂ] 𝓢(κ → V, ℂ)) (f : 𝓢(κ ⊕ κ → V, ℂ)) (N k : ℕ) :
    ∃ C : ℝ, ∀ x y, ‖x‖ ^ N * (‖y‖ ^ k * ‖T (slice x f) y‖) ≤ C := by
  obtain ⟨s, C, -, h⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (κ → V) ℂ)
    ((schwartzSeminormFamily ℂ (κ → V) ℂ (k, 0)).comp T.toLinearMap)
    (((schwartz_withSeminorms ℂ (κ → V) ℂ).continuous_seminorm (k, 0)).comp T.continuous)
  refine ⟨C * ∑ i ∈ s, 2 ^ N * SchwartzMap.seminorm ℂ (N + i.1) i.2 f, fun x y => ?_⟩
  have h1 : ‖y‖ ^ k * ‖T (slice x f) y‖ ≤ C * ∑ i ∈ s, SchwartzMap.seminorm ℂ i.1 i.2 (slice x f) := by
    refine (SchwartzMap.norm_pow_mul_le_seminorm ℂ _ k y).trans ((h (slice x f)).trans ?_)
    refine mul_le_mul_of_nonneg_left (Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_) C.2
    exact Finset.single_le_sum (f := fun i : ℕ × ℕ => SchwartzMap.seminorm ℂ i.1 i.2 (slice x f))
      (fun _ _ => apply_nonneg _ _) hi
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  rw [mul_left_comm, Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => slice_seminorm f N _ _ x) C.2

theorem slice_decay (T : 𝓢(κ → V, ℂ) →L[ℂ] 𝓢(κ → V, ℂ)) (f : 𝓢(κ ⊕ κ → V, ℂ)) (N : ℕ) :
    ∃ C : ℝ, ∀ z : κ ⊕ κ → V, ‖z‖ ^ N * ‖T (slice (z ∘ Sum.inl) f) (z ∘ Sum.inr)‖ ≤ C := by
  obtain ⟨C, h⟩ := slice_bound T f N 0
  obtain ⟨C', h'⟩ := slice_bound T f 0 N
  refine ⟨max C C', fun z => ?_⟩
  rcases le_max_iff.1 (GlobalTheory.SchwartzBox.norm_le_max_comp z) with e | e
  · refine le_max_of_le_left (le_trans ?_ (h (z ∘ Sum.inl) (z ∘ Sum.inr)))
    rw [pow_zero, one_mul]; gcongr
  · refine le_max_of_le_right (le_trans ?_ (h' (z ∘ Sum.inl) (z ∘ Sum.inr)))
    rw [pow_zero, one_mul]; gcongr

end Real

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem summable_decay (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (hf : ∀ N : ℕ, ∃ C : ℝ, ∀ z, ‖z‖ ^ N * ‖f z‖ ≤ C)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    Summable fun ξ : κ → F => pureA F f g (fun i => algebraMap F (AF F) (ξ i)) := by
  simp only [pureA_algebraMap]
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hs : Summable fun z : denomLattice F κ N => ‖f z‖ := by
    obtain ⟨C, hC⟩ := hf (Module.finrank ℤ (denomLattice F κ N) + 1)
    refine Summable.of_norm_bounded_eventually
      ((ZLattice.summable_norm_pow_inv _ _ (Nat.lt_succ_self _)).mul_left C) ?_
    refine (Set.finite_singleton (0 : denomLattice F κ N)).subset fun z hz => ?_
    by_contra h0
    apply hz
    show ‖‖f z‖‖ ≤ C * ‖z‖⁻¹ ^ _
    rw [norm_norm, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos (norm_pos_iff.2 h0) _), mul_comm]
    exact hC z
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine mul_eq_zero_of_right _ ?_
    by_contra h0
    apply hξ
    refine ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_norm_bounded ((hs.comp_injective hj).mul_right B) fun ξ => ?_
    rw [Function.comp_apply, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)

open GroundTheory.Automorphic.GJMatrix GroundTheory.Global

theorem sch_eq : schA F κ = schwartzBruhatPi F κ := rfl

def sl (a : κ → AF F) (Φ : (κ ⊕ κ → AF F) → ℂ) (u : κ → AF F) : ℂ := Φ (Sum.elim (u + a) u)

theorem sl_tensor (a : κ → AF F) (f : 𝓢(κ ⊕ κ → mixedEmbedding.mixedSpace F, ℂ)) (g : (κ ⊕ κ → Af F) → ℂ) :
    sl a (schwartzBruhatTensorPi f g) =
      schwartzBruhatTensorPi (slice (infPartPi a) f) fun u => g (Sum.elim (u + finPartPi a) u) := by
  funext u
  simp only [sl, schwartzBruhatTensorPi, slice_apply]
  congr 2 <;> funext i <;> cases i <;> try rfl
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

theorem coset_split (J) (b : κ ⊕ κ → Af F) (a : κ → Af F) :
    (fun u => finiteTensor (fun i => cosetIndicator J (b i)) (Sum.elim (u + a) u)) =
      finiteTensor (fun i => cosetIndicator J (b (.inl i) - b (.inr i))) a •
        finiteTensor fun i => cosetIndicator J (b (.inr i)) := by
  funext u
  simp only [finiteTensor, Fintype.prod_sum_type, Pi.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib, Sum.elim_inl,
    Sum.elim_inr, cosetIndicator_apply, Pi.add_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : u i - b (.inr i) ∈ idealFiniteAdeles J
  · simp only [show u i + a i - b (.inl i) = (u i - b (.inr i)) + (a i - (b (.inl i) - b (.inr i))) by ring,
      AddSubgroup.add_mem_cancel_left _ h]
    congr
  · simp [h]

abbrev rt (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

theorem sl_coset (f : 𝓢(κ ⊕ κ → mixedEmbedding.mixedSpace F, ℂ)) (J) (b : κ ⊕ κ → Af F) :
    (∀ a, sl a (schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i))) ∈ schwartzBruhatPi F κ) ∧
    Summable fun ξ : κ ⊕ κ → F => adelicFourierPi F
      (sl (rt (ξ ∘ .inl)) (schwartzBruhatTensorPi f (finiteTensor fun i => cosetIndicator J (b i)))) (rt (ξ ∘ .inr)) := by
  have m : ∀ c : κ → Af F, finiteTensor (fun i => cosetIndicator J (c i)) ∈ finiteSchwartzBruhatPi F := fun c =>
    finiteTensor_mem fun i => cosetIndicator_mem_finiteSchwartzBruhat J (c i)
  refine ⟨fun a => ?_, (summable_decay _ (slice_decay (mixedFourierPiSchwartz F) f)
      (GlobalTheory.SchwartzBox.sb_box (m fun i => b (.inl i) - b (.inr i)) (finiteFourierPi_mem (m fun i => b (.inr i))))).congr
      fun ξ => ?_⟩
  · rw [sl_tensor, coset_split]
    exact schwartzBruhatTensorPi_mem _ (Submodule.smul_mem _ _ (m _))
  · rw [sl_tensor, coset_split, adelicFourierPi_schwartzBruhatTensorPi, finiteFourierPi_smul]
    rfl

theorem sl_mem {Φ : (κ ⊕ κ → AF F) → ℂ} (h : Φ ∈ schA F (κ ⊕ κ)) : (∀ a, sl a Φ ∈ schwartzBruhatPi F κ) ∧
    Summable fun ξ : κ ⊕ κ → F => adelicFourierPi F (sl (rt (ξ ∘ .inl)) Φ) (rt (ξ ∘ .inr)) := by
  rw [sch_eq, schwartzBruhatPi_eq_cosetSpanPi] at h
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, J, b, rfl⟩ := hG
    exact sl_coset f J b
  | zero =>
    refine ⟨fun a => zero_mem _, summable_zero.congr fun ξ => ?_⟩
    exact (congrFun adelicFourierPi_zero _).symm
  | add G H _ _ hG hH =>
    refine ⟨fun a => add_mem (hG.1 a) (hH.1 a), (hG.2.add hH.2).congr fun ξ => ?_⟩
    exact (congrFun (adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (hG.1 _))
      (integrable_of_mem_schwartzBruhatPi (hH.1 _))) _).symm
  | smul c G _ hG =>
    refine ⟨fun a => Submodule.smul_mem _ c (hG.1 a), (hG.2.mul_left c).congr fun ξ => ?_⟩
    exact (congrFun (adelicFourierPi_smul c (sl (rt (ξ ∘ .inl)) G)) _).symm

theorem hasSum_sl {Φ : (κ ⊕ κ → AF F) → ℂ} (h : Φ ∈ schA F (κ ⊕ κ)) :
    HasSum (fun ξ : (κ → F) × (κ → F) => adelicFourierPi F (sl (rt ξ.1) Φ) (rt ξ.2)) (thetaSum F Φ) := by
  have s : Summable fun ξ : (κ → F) × (κ → F) => adelicFourierPi F (sl (rt ξ.1) Φ) (rt ξ.2) :=
    (Equiv.sumArrowEquivProdArrow κ κ F).summable_iff.1 (sl_mem h).2
  let e : (κ → F) × (κ → F) ≃ (κ ⊕ κ → F) :=
      { toFun := fun p => Sum.elim (p.2 + p.1) p.2
        invFun := fun z => (z ∘ Sum.inl - z ∘ Sum.inr, z ∘ Sum.inr)
        left_inv := fun p => by simp
        right_inv := fun z => by funext i; cases i <;> simp }
  have t : HasSum (fun p : (κ → F) × (κ → F) => sl (rt p.1) Φ (rt p.2)) (thetaSum F Φ) := by
    convert e.hasSum_iff.2 (hasSum_thetaSum F h) using 2 with p
    refine congrArg Φ (funext fun i => ?_)
    cases i <;> simp [e]
  refine s.hasSum_iff.2 ?_
  rw [s.tsum_prod, ← t.tsum_eq, t.summable.tsum_prod]
  exact tsum_congr fun a => (tsum_algebraMap_eq_tsum_adelicFourierPi ((sl_mem h).1 (rt a))).symm

end GlobalTheory.ThK.Dbl

end
