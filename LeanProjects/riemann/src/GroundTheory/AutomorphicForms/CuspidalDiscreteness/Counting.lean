import Mathlib
import GroundTheory.GlobalFields.Adele.Discrete

open NumberField IsDedekindDomain Set

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

variable (K : Type*) [Field K] [NumberField K]

theorem exists_pos_natCast_mul_isIntegral (k : K) : ∃ c : ℕ, 0 < c ∧ IsIntegral ℤ ((c : K) * k) := by
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic k))
  obtain ⟨c, hc | hc⟩ := Int.eq_nat_or_neg y
  · refine ⟨c, Nat.pos_of_ne_zero fun h => hy0 (by rw [hc, h, Nat.cast_zero]), ?_⟩
    have : (c : K) * k = y • k := by rw [zsmul_eq_mul, hc]; push_cast; ring
    rw [this]
    exact hyint
  · refine ⟨c, Nat.pos_of_ne_zero fun h => hy0 (by rw [hc, h, Nat.cast_zero, neg_zero]), ?_⟩
    have : (c : K) * k = -(y • k) := by rw [zsmul_eq_mul, hc]; push_cast; ring
    rw [this]
    exact hyint.neg

theorem exists_natCast_mul_mem_integralFiniteAdeles (a : FiniteAdeleRing (𝓞 K) K) :
    ∃ c : ℕ, ((c + 1 : ℕ) : FiniteAdeleRing (𝓞 K) K) * a ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles a
  obtain ⟨c, hc0, hint⟩ := exists_pos_natCast_mul_isIntegral K k
  refine ⟨c - 1, ?_⟩
  rw [Nat.sub_add_cancel hc0]
  have h1 : algebraMap K (FiniteAdeleRing (𝓞 K) K) ((c : K) * k) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    GroundTheory.Global.algebraMap_integers_mem_integralFiniteAdeles K ⟨_, hint⟩
  have h2 : ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) *
      (a - algebraMap K (FiniteAdeleRing (𝓞 K) K) k) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K :=
    Subring.mul_mem _ (natCast_mem _ _) hk
  have : ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) * a =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) ((c : K) * k) +
        ((c : ℕ) : FiniteAdeleRing (𝓞 K) K) * (a - algebraMap K (FiniteAdeleRing (𝓞 K) K) k) := by
    rw [map_mul, map_natCast]
    ring
  rw [this]
  exact Subring.add_mem _ h1 h2

theorem exists_natCast_mul_integral_of_isCompact {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)}
    (h𝒦 : IsCompact 𝒦) :
    ∃ m : ℕ, 0 < m ∧ ∀ ξ : K, algebraMap K (FiniteAdeleRing (𝓞 K) K) ξ ∈ 𝒦 →
      ∃ z : 𝓞 K, (z : K) = m * ξ := by
  set U : ℕ → Set (FiniteAdeleRing (𝓞 K) K) := fun c =>
    {a | ((c + 1 : ℕ) : FiniteAdeleRing (𝓞 K) K) * a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K}
  have hU : ∀ c, IsOpen (U c) := fun c =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const_mul _)
  have hcov : 𝒦 ⊆ ⋃ c, U c := fun a _ =>
    mem_iUnion.2 (exists_natCast_mul_mem_integralFiniteAdeles K a)
  obtain ⟨t, ht⟩ := h𝒦.elim_finite_subcover U hU hcov
  refine ⟨∏ c ∈ t, (c + 1), Finset.prod_pos fun c _ => Nat.succ_pos c, fun ξ hξ => ?_⟩
  obtain ⟨c, hct, hc⟩ := mem_iUnion₂.1 (ht hξ)
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun c => c + 1) hct
  have hmem : algebraMap K (FiniteAdeleRing (𝓞 K) K) (((∏ c ∈ t, (c + 1) : ℕ) : K) * ξ) ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
    rw [map_mul, map_natCast, hq, Nat.cast_mul, mul_comm (((c + 1 : ℕ)) : FiniteAdeleRing (𝓞 K) K),
      mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ _) hc
  obtain ⟨z, hz⟩ := GroundTheory.Global.exists_eq_of_forall_mem_adicCompletionIntegers K _ hmem
  exact ⟨z, hz⟩

open scoped Classical in

theorem exists_abs_repr_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : 𝓞 K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)),
      |(((RingOfIntegers.basis K).repr z i : ℤ) : ℝ)| ≤
        C * ‖mixedEmbedding K (z : K)‖ := by
  set Lc := LinearMap.toContinuousLinearMap (mixedEmbedding.latticeBasis K).equivFun.toLinearMap
  refine ⟨‖Lc‖, norm_nonneg _, fun z i => ?_⟩
  have hval : Lc (mixedEmbedding K (z : K)) i = (((RingOfIntegers.basis K).repr z i : ℤ) : ℝ) := by
    change (mixedEmbedding.latticeBasis K).equivFun (mixedEmbedding K (z : K)) i = _
    rw [Module.Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply]
    have := integralBasis_repr_apply K z i
    rw [show (z : K) = algebraMap (𝓞 K) K z from rfl, this]
    simp
  rw [← hval, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ i).trans (Lc.le_opNorm _)

theorem exists_ncard_integers_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.Finite ∧
      (({z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.ncard : ℝ) ≤
        C * (1 + T) ^ Module.finrank ℚ K) := by
  classical
  obtain ⟨C₀, hC₀, hrepr⟩ := exists_abs_repr_le K
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hd : Fintype.card ι = Module.finrank ℚ K := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  refine ⟨(3 + 2 * C₀) ^ Module.finrank ℚ K, by positivity, fun T hT => ?_⟩
  set N : ℕ := ⌈C₀ * T⌉₊
  set box : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N
  set c : 𝓞 K → ι → ℤ := fun z i => (RingOfIntegers.basis K).repr z i
  have hmaps : ∀ z ∈ {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}, c z ∈ (box : Set (ι → ℤ)) := by
    intro z hz
    have hnorm : ‖mixedEmbedding K (z : K)‖ ≤ T := by
      rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le _ _ fun w _ => ?_
      rw [mixedEmbedding.normAtPlace_apply]
      exact hz w
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have h1 := (hrepr z i).trans (mul_le_mul_of_nonneg_left hnorm hC₀)
    have h2 : C₀ * T ≤ N := Nat.le_ceil _
    have h3 : |(c z i : ℝ)| ≤ N := h1.trans h2
    rw [abs_le] at h3
    rw [Finset.mem_Icc]
    constructor <;> [exact_mod_cast (by linarith [h3.1] : (-(N : ℝ)) ≤ c z i);
      exact_mod_cast h3.2]
  have hinj : InjOn c {z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T} := by
    intro z _ z' _ h
    refine (RingOfIntegers.basis K).repr.injective (Finsupp.ext fun i => ?_)
    exact congrFun h i
  have hfin : (box : Set (ι → ℤ)).Finite := Finset.finite_toSet _
  refine ⟨hfin.of_injOn hmaps hinj, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn c hmaps hinj hfin
  rw [Set.ncard_coe_finset, Fintype.card_piFinset] at hcard
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ] at hcard
  have hN : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [hN, hd] at hcard
  have hNle : (2 * N + 1 : ℝ) ≤ (3 + 2 * C₀) * (1 + T) := by
    have : (N : ℝ) ≤ C₀ * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    nlinarith
  calc (({z : 𝓞 K | ∀ w : InfinitePlace K, w (z : K) ≤ T}.ncard : ℕ) : ℝ)
      ≤ ((2 * N + 1) ^ Module.finrank ℚ K : ℕ) := by exact_mod_cast hcard
    _ = (2 * N + 1 : ℝ) ^ Module.finrank ℚ K := by push_cast; ring
    _ ≤ ((3 + 2 * C₀) * (1 + T)) ^ Module.finrank ℚ K := by gcongr
    _ = (3 + 2 * C₀) ^ Module.finrank ℚ K * (1 + T) ^ Module.finrank ℚ K := mul_pow _ _ _

variable {K}

def ratGLBox (n : ℕ) (𝒦 : Set (FiniteAdeleRing (𝓞 K) K)) (T : ℝ) : Set (GL (Fin n) K) :=
  {γ | ∀ i j, algebraMap K (FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin n) (Fin n) K) i j) ∈ 𝒦 ∧
    ∀ w : InfinitePlace K, w ((γ : Matrix (Fin n) (Fin n) K) i j) ≤ T}

theorem exists_ncard_ratGLBox_le (n : ℕ) {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)} (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ T : ℝ, 0 ≤ T →
      (ratGLBox n 𝒦 T).Finite ∧ ((ratGLBox n 𝒦 T).ncard : ℝ) ≤ C * (1 + T) ^ N := by
  classical
  obtain ⟨m, hm, hmint⟩ := exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₂, hC₂, hcount⟩ := exists_ncard_integers_le K
  set d := Module.finrank ℚ K
  refine ⟨(C₂ * (m : ℝ) ^ d) ^ (n * n), d * (n * n), fun T hT => ?_⟩
  have hmT : 0 ≤ (m : ℝ) * T := by positivity
  obtain ⟨hfinS, hcardS⟩ := hcount (m * T) hmT
  set F := hfinS.toFinset
  set Φ : GL (Fin n) K → Fin n → Fin n → 𝓞 K := fun γ i j =>
    if h : ∃ z : 𝓞 K, (z : K) = m * (γ : Matrix (Fin n) (Fin n) K) i j then h.choose else 0
  set box : Finset (Fin n → Fin n → 𝓞 K) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  have hΦ : ∀ γ ∈ ratGLBox n 𝒦 T, ∀ i j,
      ((Φ γ i j : 𝓞 K) : K) = m * (γ : Matrix (Fin n) (Fin n) K) i j := by
    intro γ hγ i j
    have h := hmint _ (hγ i j).1
    simp only [Φ, dif_pos h]
    exact h.choose_spec
  have hmaps : ∀ γ ∈ ratGLBox n 𝒦 T, Φ γ ∈ (box : Set (Fin n → Fin n → 𝓞 K)) := by
    intro γ hγ
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    intro w
    rw [hΦ γ hγ i j, map_mul, InfinitePlace.map_natCast]
    exact mul_le_mul_of_nonneg_left ((hγ i j).2 w) (Nat.cast_nonneg m)
  have hinj : InjOn Φ (ratGLBox n 𝒦 T) := by
    intro γ hγ γ' hγ' h
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h1 := hΦ γ hγ i j
    have h2 := hΦ γ' hγ' i j
    rw [show Φ γ i j = Φ γ' i j from congrFun (congrFun h i) j, h2] at h1
    have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    exact (mul_left_cancel₀ hm0 h1).symm
  have hfin : (box : Set (Fin n → Fin n → 𝓞 K)).Finite := Finset.finite_toSet _
  refine ⟨hfin.of_injOn hmaps hinj, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin
  rw [Set.ncard_coe_finset] at hcard
  simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hcard
  have hF : (F.card : ℝ) ≤ C₂ * (m : ℝ) ^ d * (1 + T) ^ d := by
    rw [← Set.ncard_eq_toFinset_card _ hfinS]
    refine hcardS.trans ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 1 + (m : ℝ) * T ≤ m * (1 + T) := by nlinarith
    calc C₂ * (1 + (m : ℝ) * T) ^ d ≤ C₂ * ((m : ℝ) * (1 + T)) ^ d := by gcongr
      _ = C₂ * (m : ℝ) ^ d * (1 + T) ^ d := by rw [mul_pow]; ring
  calc ((ratGLBox n 𝒦 T).ncard : ℝ) ≤ (((F.card ^ n) ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (F.card : ℝ) ^ (n * n) := by push_cast; rw [← pow_mul]
    _ ≤ (C₂ * (m : ℝ) ^ d * (1 + T) ^ d) ^ (n * n) := by gcongr
    _ = (C₂ * (m : ℝ) ^ d) ^ (n * n) * (1 + T) ^ (d * (n * n)) := by rw [mul_pow, ← pow_mul]

end CuspidalSpectrum

end

end GroundTheory.Automorphic
