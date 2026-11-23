import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsBoundedMultipleNearInteger
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.NearPrim

theorem exists_reduce (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C := by
  classical
  let b := integralBasis E
  refine ⟨∑ i, ‖canonicalEmbedding E (b i)‖, fun x => ⟨∑ i, ⌊b.repr x i⌋ • b i, ?_, ?_⟩⟩
  · refine IsIntegral.sum _ fun i _ => IsIntegral.zsmul ?_ _
    simp only [b, integralBasis_apply]
    exact RingOfIntegers.isIntegral_coe _
  · have h : x - ∑ i, ⌊b.repr x i⌋ • b i = ∑ i, (Int.fract (b.repr x i) : ℚ) • b i := by
      conv_lhs => rw [← b.sum_repr x]
      rw [b.sum_repr x]
      nth_rewrite 1 [← b.sum_repr x]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    rw [h, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_rat_smul, norm_smul]
    have h0 := Int.fract_nonneg (b.repr x i)
    have h1 := (Int.fract_lt_one (b.repr x i)).le
    have : ‖(Int.fract (b.repr x i) : ℚ)‖ ≤ 1 := by
      rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast h0)]
      exact_mod_cast h1
    exact mul_le_of_le_one_left (norm_nonneg _) this

theorem exists_approx (E : Type) [Field E] [NumberField E] :
    ∃ M : ℕ, ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer
  | (apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimultaneousDiophantineApprox.exists_bounded_multiple_near_integer ..)

theorem exists_min {E : Type} [Field E] [NumberField E] (S : Set E) (d : ℤ) (hd : d ≠ 0)
    (hS : ∀ x ∈ S, IsIntegral ℤ ((d : E) * x)) (h1 : (1 : E) ∈ S) :
    ∃ α ∈ S, ‖canonicalEmbedding E α‖ ≤ 1 ∧
      ∀ x ∈ S, ‖canonicalEmbedding E α‖ ≤ ‖canonicalEmbedding E x‖ := by
  have hfin : {x ∈ S | ‖canonicalEmbedding E x‖ ≤ 1}.Finite := by
    refine Set.Finite.of_finite_image (f := fun x => (d : E) * x)
      ((Embeddings.finite_of_norm_le E ℂ |(d : ℝ)|).subset ?_) ?_
    · rintro _ ⟨x, ⟨hx, hx1⟩, rfl⟩
      refine ⟨hS x hx, fun φ => ?_⟩
      have := (canonicalEmbedding.norm_le_iff x 1).1 hx1 φ
      rw [map_mul, norm_mul, map_intCast, Complex.norm_intCast]
      exact mul_le_of_le_one_right (abs_nonneg _) this
    · intro x _ y _ h
      exact mul_left_cancel₀ (Int.cast_ne_zero.2 hd) h
  have hone : ‖canonicalEmbedding E 1‖ ≤ 1 := (canonicalEmbedding.norm_le_iff 1 1).2 (by simp)
  obtain ⟨α, hα, hmin⟩ := Set.exists_min_image _ (fun x => ‖canonicalEmbedding E x‖) hfin
    ⟨1, h1, hone⟩
  refine ⟨α, hα.1, hα.2, fun x hx => ?_⟩
  by_cases h : ‖canonicalEmbedding E x‖ ≤ 1
  · exact hmin x ⟨hx, h⟩
  · exact hα.2.trans (not_le.1 h).le

theorem exists_den {E : Type} [Field E] [NumberField E] {k : ℕ} {m : Type} [Fintype m]
    (W : Matrix (Fin k) m E) (hW : LinearIndependent E (fun i => W i)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ s : Fin k → E, (∀ j, IsIntegral ℤ ((s ᵥ* W) j)) →
      ∀ i, IsIntegral ℤ ((d : E) * s i) := by
  classical
  have hinj : LinearMap.ker (W.vecMulLinear) = ⊥ :=
    LinearMap.ker_eq_bot.2 (Matrix.vecMul_injective_iff.2 hW)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : m × Fin k => g (Pi.single p.1 1) p.2)
  refine ⟨d, hd, fun s hs i => ?_⟩
  have h1 : g (s ᵥ* W) = s := by simpa using LinearMap.congr_fun hg s
  have h2 : s ᵥ* W = ∑ j, (s ᵥ* W) j • (Pi.single j 1 : m → E) := pi_eq_sum_univ' _
  rw [← h1, h2, map_sum, Finset.sum_apply, Finset.mul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  refine (hs j).mul ?_
  have := hint _ (Finset.mem_image.2 ⟨(j, i), Finset.mem_univ _, rfl⟩)
  simpa [zsmul_eq_mul] using this

theorem exists_rows {E : Type} [Field E] [NumberField E] {k : ℕ} (L : AddSubgroup (Fin k → E))
    (hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L) (d : ℤ) (hd : d ≠ 0)
    (hL : ∀ s ∈ L, ∀ i, IsIntegral ℤ ((d : E) * s i)) (C : ℝ)
    (hC : ∀ x : E, ∃ y : E, IsIntegral ℤ y ∧ ‖canonicalEmbedding E (x - y)‖ ≤ C) (i : Fin k) :
    ∃ a ∈ L, (∀ j, i < j → a j = 0) ∧ a i ≠ 0 ∧ (∀ j, ‖canonicalEmbedding E (a j)‖ ≤ max 1 C) ∧
      ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i)‖ ≤ ‖canonicalEmbedding E (s i)‖ := by
  classical
  obtain ⟨α, ⟨hα0, a, haL, ha0, rfl⟩, hα1, hmin⟩ := exists_min
    {x : E | x ≠ 0 ∧ ∃ s ∈ L, (∀ j, i < j → s j = 0) ∧ s i = x} d hd
    (by rintro _ ⟨-, s, hs, -, rfl⟩; exact hL s hs i)
    ⟨one_ne_zero, Pi.single i 1, hO _ (fun j => by
      by_cases h : j = i
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero), fun j hj => by simp [hj.ne'], by simp⟩
  choose y hy hyC using hC
  refine ⟨a - fun j => if j < i then y (a j) else 0, L.sub_mem haL (hO _ fun j => ?_),
    fun j hj => ?_, ?_, fun j => ?_, fun s hs hs0 hsi => ?_⟩
  · split_ifs
    · exact hy _
    · exact isIntegral_zero
  · simp [ha0 j hj, not_lt.2 hj.le]
  · simpa using hα0
  · rcases lt_trichotomy j i with h | rfl | h
    · simp only [Pi.sub_apply, if_pos h]
      exact (hyC _).trans (le_max_right _ _)
    · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
      exact hα1.trans (le_max_left _ _)
    · simp [ha0 j h, not_lt.2 h.le]
  · simp only [Pi.sub_apply, lt_irrefl, if_false, sub_zero]
    exact hmin _ ⟨hsi, s, hs, hs0, rfl⟩

theorem integral_coord {E : Type} [Field E] [NumberField E] {k : ℕ}
    (L : AddSubgroup (Fin k → E))
    (hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L) (M : ℕ)
    (hM : ∀ x : E, ∃ (m : ℕ) (y : E), 0 < m ∧ m ≤ M ∧ IsIntegral ℤ y ∧
      ‖canonicalEmbedding E (m * x - y)‖ < 1)
    (a : Matrix (Fin k) (Fin k) E) (haL : ∀ i, a i ∈ L) (ha0 : ∀ i j, i < j → a i j = 0)
    (hai : ∀ i, a i i ≠ 0)
    (hmin : ∀ i, ∀ s ∈ L, (∀ j, i < j → s j = 0) → s i ≠ 0 →
        ‖canonicalEmbedding E (a i i)‖ ≤ ‖canonicalEmbedding E (s i)‖) (p : ℕ) (hp : p ≤ k) :
    ∀ t : Fin k → E, (∀ j : Fin k, p ≤ j → t j = 0) → t ᵥ* a ∈ L →
      ∀ i, IsIntegral ℤ (((M.factorial ^ p : ℕ) : E) * t i) := by
  classical
  induction p with
  | zero =>
    intro t ht _ i
    rw [ht i (Nat.zero_le _), mul_zero]
    exact isIntegral_zero
  | succ p ih =>
    intro t ht hL i
    let q : Fin k := ⟨p, hp⟩
    obtain ⟨m, y, hm0, hmM, hy, hlt⟩ := hM (t q)
    set t' : Fin k → E := (m : E) • t - y • Pi.single q 1 with ht'
    have ht'L : t' ᵥ* a ∈ L := by
      rw [ht', sub_vecMul, smul_vecMul, smul_vecMul, single_one_vecMul]
      exact L.sub_mem (hsm _ (isIntegral_natCast m) _ hL) (hsm _ hy _ (haL q))
    have hz : ∀ j, q < j → t' j = 0 := fun j hj => by
      simp [ht', hj.ne', ht j hj]
    have hq : t' q = m * t q - y := by simp [ht']
    have hs : ∀ j, q ≤ j → (t' ᵥ* a) j = t' j * a j j := by
      intro j hj
      rw [vecMul, dotProduct]
      refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
      rcases lt_or_gt_of_ne hl with h | h
      · rw [ha0 l j h, mul_zero]
      · rw [hz l (hj.trans_lt h), zero_mul]
    have hq0 : t' q = 0 := by
      by_contra hne
      have h1 := hmin q _ ht'L (fun j hj => by rw [hs j hj.le, hz j hj, zero_mul])
        (by rw [hs q le_rfl]; exact mul_ne_zero hne (hai q))
      rw [hs q le_rfl, map_mul, hq] at h1
      have h2 : 0 < ‖canonicalEmbedding E (a q q)‖ := by
        rw [norm_pos_iff]
        exact fun h => hai q (canonicalEmbedding_injective E (h.trans (map_zero _).symm))
      have h3 := norm_mul_le (canonicalEmbedding E (m * t q - y)) (canonicalEmbedding E (a q q))
      nlinarith
    have h := ih (by omega) t' (fun j hj => by
      rcases (show q ≤ j from hj).eq_or_lt with rfl | h
      · exact hq0
      · exact hz j h) ht'L i
    obtain ⟨e, he⟩ := Nat.dvd_factorial hm0 hmM
    have hint : IsIntegral ℤ ((Pi.single q 1 : Fin k → E) i) := by
      by_cases h : i = q
      · subst h; simpa using isIntegral_one
      · simpa [h] using isIntegral_zero
    have : ((M.factorial ^ (p + 1) : ℕ) : E) * t i =
        (e : E) * (((M.factorial ^ p : ℕ) : E) * t' i +
          ((M.factorial ^ p : ℕ) : E) * (y * (Pi.single q 1 : Fin k → E) i)) := by
      rw [pow_succ, Nat.cast_mul]
      nth_rewrite 2 [he]
      simp only [ht', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]
    exact (isIntegral_natCast e).mul (h.add ((isIntegral_natCast _).mul (hy.mul hint)))

end GlobalTheory.SW.NearPrim

namespace GlobalTheory.SW

open NearPrim in

theorem exists_nearly_primitive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (k : ℕ), ∃ (c : ℕ) (C : ℝ), 0 < c ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin k) m E), IntM W → LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin k) (Fin k) E, a.det ≠ 0 ∧ (∀ (τ : E →+* ℂ) i j, ‖τ (a i j)‖ ≤ C) ∧ IntM (a * W) ∧ ∀ t : Fin k → E, (∀ j, IsIntegral ℤ ((t ᵥ* (a * W)) j)) → ∀ i, IsIntegral ℤ ((c : E) * t i) := by
  intro E _ _ _ k
  obtain ⟨C, hC⟩ := exists_reduce E
  obtain ⟨M, hM⟩ := exists_approx E
  refine ⟨M.factorial ^ k, max 1 C, pow_pos M.factorial_pos _, fun m _ W hW hind => ?_⟩
  obtain ⟨d, hd, hden⟩ := exists_den W hind
  let L : AddSubgroup (Fin k → E) :=
    { carrier := {s | ∀ j, IsIntegral ℤ ((s ᵥ* W) j)}
      add_mem' := fun {s t} hs ht j => by rw [add_vecMul]; exact (hs j).add (ht j)
      zero_mem' := fun j => by rw [zero_vecMul]; exact isIntegral_zero
      neg_mem' := fun {s} hs j => by rw [neg_vecMul]; exact (hs j).neg }
  have hO : ∀ s : Fin k → E, (∀ i, IsIntegral ℤ (s i)) → s ∈ L := fun s hs j =>
    IsIntegral.sum (s := Finset.univ) (fun i => s i * W i j) fun i _ => (hs i).mul (hW i j)
  have hsm : ∀ y : E, IsIntegral ℤ y → ∀ s ∈ L, y • s ∈ L := fun y hy s hs j => by
    rw [smul_vecMul]; exact hy.mul (hs j)
  choose a haL ha0 hai haC hmin using exists_rows L hO d hd hden C hC
  refine ⟨Matrix.of a, ?_, fun τ i j => (canonicalEmbedding.norm_le_iff _ _).1 (haC i j) τ,
    fun i j => haL i j, fun t ht => ?_⟩
  · rw [Matrix.det_of_lowerTriangular (Matrix.of a) (fun i j h => ha0 i j h)]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hai i
  · refine integral_coord L hsm M hM (Matrix.of a) haL ha0 hai hmin k le_rfl t
      (fun j hj => absurd j.2 (not_lt.2 hj)) fun j => ?_
    rw [vecMul_vecMul]
    exact ht j

end GlobalTheory.SW
