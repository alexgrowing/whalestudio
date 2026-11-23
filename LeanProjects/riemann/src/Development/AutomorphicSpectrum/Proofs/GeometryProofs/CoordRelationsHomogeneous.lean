import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsCoordRatioBoundStatement
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FormFamilies
open MvPolynomial

theorem aeval_mul_homog {σ R : Type*} [CommRing R] [Algebra ℤ R] {P : MvPolynomial σ ℤ} {n : ℕ}
    (hP : P.IsHomogeneous n) (a : R) (x : σ → R) :
    aeval (fun j => a * x j) P = a ^ n * aeval x P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp hd)
  have : ∏ i ∈ d.support, (a * x i) ^ d i = a ^ n * ∏ i ∈ d.support, x i ^ d i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← hd']
    rfl
  rw [this]
  ring

theorem ringHom_aevalZ {σ A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] [Algebra ℤ A'] (f : A →+* A')
    (z : σ → A) (g : MvPolynomial σ ℤ) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

section Val
variable {Ω : Type} [Field Ω]

theorem exists_ratio_mem (W : ValuationSubring Ω) {κ : Type*} [Finite κ] (x : κ → Ω)
    (h : ∃ j, x j ≠ 0) : ∃ c, x c ≠ 0 ∧ ∀ j, x j / x c ∈ W :=
  _root_.UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main W x h

theorem charZero_residue (W : ValuationSubring Ω) (hW : ∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ W)
    [CharZero Ω] : CharZero (IsLocalRing.ResidueField W) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr h0
  have hu : IsUnit (n : W) := by
    refine IsUnit.of_mul_eq_one ⟨(n : Ω)⁻¹, hW n h0⟩ ?_
    apply Subtype.ext
    simp [hnΩ]
  have h1 : IsLocalRing.residue W (n : W) = 0 := by simpa using hn
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at h1
  exact h1 hu
end Val

section Pts
variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  (y : (Σ k, J k) → Ω)

theorem ne_zero_of_pt {L : Type} [Field L] {z : (Σ k, J k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) {p : Σ k, J k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hm : (X p : MRing J) ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  simpa using hz.2 _ hm

theorem aeval_ratio_eq_zero (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : MRing J}
    (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h1 := congrArg (eval (fun k => (y ⟨k, c k⟩)⁻¹)) h0
  rw [map_zero] at h1
  have h2 := ringHom_aevalZ (eval (fun k => (y ⟨k, c k⟩)⁻¹))
    (fun p : Σ k, J k => (C (y p) * X p.1 : MvPolynomial K Ω)) f
  have h3 : (fun p : Σ k, J k => eval (fun k => (y ⟨k, c k⟩)⁻¹)
      (C (y p) * X p.1 : MvPolynomial K Ω)) = fun p => y p / y ⟨p.1, c p.1⟩ := by
    funext p
    simp [div_eq_mul_inv]
  rw [h3] at h2
  rw [← h2]
  exact h1

theorem ratio_pt_mem (W : ValuationSubring Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hcW : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ W) :
    (fun p => IsLocalRing.residue W ⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩) ∈
      Small.ptsOver (IsLocalRing.ResidueField W) (mCoordIdeal y) := by
  constructor
  · intro k
    refine ⟨c k, ?_⟩
    have h1 : (⟨y ⟨k, c k⟩ / y ⟨k, c k⟩, hcW ⟨k, c k⟩⟩ : W) = 1 :=
      Subtype.ext (by simp [hc k])
    simp only [h1, map_one]
    exact one_ne_zero
  · intro f hf
    have h2 := @ringHom_aevalZ _ _ _ _ _ _ (Ring.toIntAlgebra _) (IsLocalRing.residue W)
      (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f
    rw [← h2]
    have h3 := ringHom_aevalZ W.subtype
      (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f
    have h4 : aeval (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f = 0 := by
      apply Subtype.ext
      exact h3.trans (aeval_ratio_eq_zero y c hc hf)
    rw [h4, map_zero]

theorem rename_mem (k₀ : K) {P : MvPolynomial (J k₀) ℤ} {n : ℕ} (hP : P.IsHomogeneous n)
    (h0 : aeval (fun j => y ⟨k₀, j⟩) P = 0) : rename (Sigma.mk k₀) P ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_rename]
  have e : ((fun p : Σ k, J k => (C (y p) * X p.1 : MvPolynomial K Ω)) ∘ Sigma.mk k₀) =
      fun j => (X k₀ : MvPolynomial K Ω) * C (y ⟨k₀, j⟩) := by
    funext j
    simp [mul_comm]
  rw [e, aeval_mul_homog hP]
  have h1 := ringHom_aevalZ (C : Ω →+* MvPolynomial K Ω) (fun j => y ⟨k₀, j⟩) P
  rw [← h1, h0, map_zero, mul_zero]
end Pts

section Homog
variable {σ : Type*}

def homogAt (i : σ) (G : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ m ∈ Finset.range (G.totalDegree + 1), X i ^ (G.totalDegree - m) * homogeneousComponent m G

theorem homogAt_isHomogeneous (i : σ) (G : MvPolynomial σ ℤ) :
    (homogAt i G).IsHomogeneous G.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hle : m ≤ G.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h := (isHomogeneous_X_pow (R := ℤ) i (G.totalDegree - m)).mul
    (homogeneousComponent_isHomogeneous m G)
  rwa [Nat.sub_add_cancel hle] at h

theorem aeval_homogAt {R : Type*} [Field R] (x : σ → R) (i : σ) (hi : x i ≠ 0)
    (G : MvPolynomial σ ℤ) :
    aeval x (homogAt i G) = x i ^ G.totalDegree * aeval (fun j => x j / x i) G := by
  have h0 : aeval (fun j => x j / x i) G = ∑ m ∈ Finset.range (G.totalDegree + 1),
      aeval (fun j => x j / x i) (homogeneousComponent m G) := by
    rw [← map_sum, sum_homogeneousComponent]
  rw [h0, homogAt, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m ≤ G.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h2 := aeval_mul_homog (homogeneousComponent_isHomogeneous m G) (x i)
    (fun j => x j / x i)
  have hx : (fun j => x i * (x j / x i)) = x := by
    funext j
    field_simp
  rw [hx] at h2
  rw [map_mul, map_pow, aeval_X, h2, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem exists_clear {Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range r)) :
    ∃ (N : ℕ) (A : MvPolynomial σ ℤ), N ≠ 0 ∧ (N : Ω) * b = aeval r A := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, X j, one_ne_zero, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, C q.num, q.den_ne_zero, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    rw [eq_ratCast, Rat.cast_def, aeval_C]
    simp only [eq_intCast]
    field_simp
  | add x w _ _ hx hw =>
    obtain ⟨N1, A1, h1, e1⟩ := hx
    obtain ⟨N2, A2, h2, e2⟩ := hw
    refine ⟨N1 * N2, C (N2 : ℤ) * A1 + C (N1 : ℤ) * A2, mul_ne_zero h1 h2, ?_⟩
    simp only [map_add, map_mul, aeval_C, eq_intCast, Int.cast_natCast, map_natCast, ← e1, ← e2, Nat.cast_mul]
    ring
  | mul x w _ _ hx hw =>
    obtain ⟨N1, A1, h1, e1⟩ := hx
    obtain ⟨N2, A2, h2, e2⟩ := hw
    refine ⟨N1 * N2, A1 * A2, mul_ne_zero h1 h2, ?_⟩
    simp only [map_mul, ← e1, ← e2, Nat.cast_mul]
    ring
end Homog

section Main
variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  (y : (Σ k, J k) → Ω)

theorem vanish {L : Type} [Field L] {z : (Σ k, J k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) {k₀ : K} (i : J k₀) (hy : y ⟨k₀, i⟩ ≠ 0)
    (hzi : z ⟨k₀, i⟩ ≠ 0) (G : MvPolynomial (J k₀) ℤ)
    (hG : aeval (fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) G = 0) :
    aeval (fun j => z ⟨k₀, j⟩ / z ⟨k₀, i⟩) G = 0 := by
  have hy0 : aeval (fun j => y ⟨k₀, j⟩) (homogAt i G) = 0 := by
    rw [aeval_homogAt (fun j => y ⟨k₀, j⟩) i hy, hG, mul_zero]
  have hm := rename_mem y k₀ (homogAt_isHomogeneous i G) hy0
  have h1 := hz.2 _ hm
  rw [aeval_rename] at h1
  have h2 := aeval_homogAt (fun j => z ⟨k₀, j⟩) i hzi G
  have h3 : aeval (fun j => z ⟨k₀, j⟩) (homogAt i G) = 0 := h1
  rw [h3] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hzi)

def ratio (k₀ : K) (i : J k₀) : J k₀ → Ω := fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩

def chartSub [CharZero Ω] (k₀ : K) (i : J k₀) : Subring Ω :=
  (Algebra.adjoin ℚ (Set.range (ratio y k₀ i))).toSubring

def ratioA [CharZero Ω] (k₀ : K) (i : J k₀) : J k₀ → chartSub y k₀ i :=
  fun j => ⟨ratio y k₀ i j, Algebra.subset_adjoin ⟨j, rfl⟩⟩

theorem coe_aeval_ratioA [CharZero Ω] (k₀ : K) (i : J k₀) (f : MvPolynomial (J k₀) ℤ) :
    ((aeval (ratioA y k₀ i) f : chartSub y k₀ i) : Ω) = aeval (ratio y k₀ i) f :=
  ringHom_aevalZ (chartSub y k₀ i).subtype (ratioA y k₀ i) f

theorem span_top [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ))
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0)
    (i : J k₀) (hi : y ⟨k₀, i⟩ ≠ 0) :
    Ideal.span ((fun f => aeval (ratioA y k₀ i) f) '' S) = ⊤ := by
  by_contra hne
  obtain ⟨W, hAW, hsub⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hinv : ∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ W := by
    intro n _
    have h1 : ((n : Ω))⁻¹ ∈ chartSub y k₀ i := by
      have h2 := (Algebra.adjoin ℚ (Set.range (ratio y k₀ i))).algebraMap_mem ((n : ℚ)⁻¹)
      have h3 : ((n : Ω))⁻¹ ∈ Algebra.adjoin ℚ (Set.range (ratio y k₀ i)) := by simpa using h2
      exact h3
    exact hAW h1
  have hblock : ∀ k, ∃ c : J k, y ⟨k, c⟩ ≠ 0 ∧ ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ W :=
    fun k => exists_ratio_mem W _ (hy k)
  choose c0 hc0 hcW0 using hblock
  classical
  let c : ∀ k, J k := Function.update c0 k₀ i
  have hck : c k₀ = i := Function.update_self _ _ _
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hck]
      exact hi
    · rw [show c k = c0 k from Function.update_of_ne h _ _]
      exact hc0 k
  have hcW : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ W := by
    rintro ⟨k, j⟩
    by_cases h : k = k₀
    · subst h
      simp only [hck]
      exact hAW (ratioA y k i j).2
    · simp only [show c k = c0 k from Function.update_of_ne h _ _]
      exact hcW0 k j
  haveI := charZero_residue W hinv
  obtain ⟨f, hfS, hf⟩ := H (IsLocalRing.ResidueField W) _ (ratio_pt_mem y W c hc hcW)
  apply hf
  have hnon : (aeval (ratio y k₀ i) f : Ω) ∈ W.nonunits := by
    have h1 := hsub ⟨aeval (ratioA y k₀ i) f, Ideal.subset_span ⟨f, hfS, rfl⟩, rfl⟩
    rwa [Subring.subtype_apply, coe_aeval_ratioA] at h1
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnon
  let w : J k₀ → W := fun j => ⟨y ⟨k₀, j⟩ / y ⟨k₀, c k₀⟩, hcW ⟨k₀, j⟩⟩
  have e1 : (aeval w f : W) = ⟨aeval (ratio y k₀ i) f, hmem⟩ := by
    apply Subtype.ext
    have h3 := ringHom_aevalZ W.subtype w f
    have h4 : (fun p => W.subtype (w p)) = ratio y k₀ i := by
      funext j
      simp [w, ratio, hck]
    rw [h4] at h3
    exact h3
  have e2 := ringHom_aevalZ (IsLocalRing.residue W) w f
  change aeval (fun i' => IsLocalRing.residue W (w i')) f = 0
  rw [← e2, e1]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax

theorem exists_finset_at [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ)) (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n)
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0)
    (i : J k₀) (hi : y ⟨k₀, i⟩ ≠ 0) :
    ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → z ⟨k₀, i⟩ ≠ 0 →
          ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
  classical
  have htop := span_top y k₀ hy S H i hi
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 htop
  obtain ⟨T, hT, rfl⟩ := Finset.subset_set_image_iff.1 hs
  refine ⟨T, hT, ?_⟩
  intro L _ _ z hz hzi
  by_contra hall
  push_neg at hall
  have key : ∀ b ∈ Ideal.span ((T.image fun f => aeval (ratioA y k₀ i) f :
      Finset (chartSub y k₀ i)) : Set (chartSub y k₀ i)),
      ∃ (N : ℕ) (G : MvPolynomial (J k₀) ℤ), N ≠ 0 ∧ (N : Ω) * (b : Ω) = aeval (ratio y k₀ i) G ∧
        aeval (fun j => z ⟨k₀, j⟩ / z ⟨k₀, i⟩) G = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨f, hf, rfl⟩ := hx
      refine ⟨1, f, one_ne_zero, by rw [Nat.cast_one, _root_.one_mul, coe_aeval_ratioA], ?_⟩
      obtain ⟨n, hn⟩ := hS f (hT hf)
      have h1 := aeval_mul_homog hn (z ⟨k₀, i⟩)⁻¹ (fun j => z ⟨k₀, j⟩)
      rw [hall f hf, mul_zero] at h1
      rw [← h1]
      congr 2
      funext j
      rw [div_eq_inv_mul]
    | zero => exact ⟨1, 0, one_ne_zero, by simp, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨N1, A1, h1, e1, v1⟩ := hx
      obtain ⟨N2, A2, h2, e2, v2⟩ := hw
      refine ⟨N1 * N2, C (N2 : ℤ) * A1 + C (N1 : ℤ) * A2, mul_ne_zero h1 h2, ?_, ?_⟩
      · simp only [map_add, map_mul, aeval_C, eq_intCast, Int.cast_natCast, map_natCast, ← e1, ← e2,
          Nat.cast_mul, AddMemClass.coe_add]
        ring
      · simp only [map_add, map_mul, v1, v2, mul_zero, add_zero]
    | smul a x _ hx =>
      obtain ⟨N1, A1, h1, e1⟩ := exists_clear (ratio y k₀ i) a.2
      obtain ⟨N2, A2, h2, e2, v2⟩ := hx
      refine ⟨N1 * N2, A1 * A2, mul_ne_zero h1 h2, ?_, ?_⟩
      · simp only [map_mul, ← e1, ← e2, Nat.cast_mul, smul_eq_mul, MulMemClass.coe_mul]
        ring
      · simp only [map_mul, v2, mul_zero]
  obtain ⟨N, G, hN, e1, e2⟩ := key 1 (by rw [hspan]; trivial)
  have hG : aeval (ratio y k₀ i) (G - C (N : ℤ)) = 0 := by
    simp [← e1]
  have h1 := vanish y hz i hi hzi _ hG
  simp only [map_sub, e2, aeval_C, eq_intCast, zero_sub, neg_eq_zero, Int.cast_natCast, map_natCast] at h1
  exact hN (Nat.cast_eq_zero.mp h1)

theorem exists_finset [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ)) (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n)
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0) :
    ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
  classical
  have hi : ∀ i : J k₀, ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → z ⟨k₀, i⟩ ≠ 0 →
          ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
    intro i
    by_cases h : y ⟨k₀, i⟩ = 0
    · exact ⟨∅, by simp, fun L _ _ z hz hzi => absurd h (ne_zero_of_pt y hz hzi)⟩
    · exact exists_finset_at y k₀ hy S hS H i h
  choose T hT hT' using hi
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, -, hfi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hf)
    exact hT i hfi
  · intro L _ _ z hz
    obtain ⟨i, hi'⟩ := hz.1 k₀
    obtain ⟨f, hf, hne⟩ := hT' i L z hz hi'
    exact ⟨f, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hf⟩, hne⟩
end Main

theorem finite_families : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE k
  have hy : ∀ k', ∃ j, y ⟨k', j⟩ ≠ 0 := by
    intro k'
    obtain ⟨c, hc, -⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k', Finset.prod_ne_zero_iff.mp hc k' (Finset.mem_univ _)⟩
  let Fam : ℕ → (J k → MvPolynomial (J k₀) ℤ) → Prop := fun n F =>
    (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j j', aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, j'⟩ =
        aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j') * y ⟨k, j⟩
  let S : Set (MvPolynomial (J k₀) ℤ) := {f | ∃ n F j, Fam n F ∧ f = F j}
  have hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n := by
    rintro f ⟨n, F, j, hF, rfl⟩
    exact ⟨n, hF.1 j⟩
  have H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
    intro L _ _ z hz
    obtain ⟨i, hi⟩ := hz.1 k₀
    obtain ⟨c, hc⟩ := hz.1 k
    obtain ⟨n, F, hom, rel, hne⟩ := GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE L z hz i k c hi hc
    have yc : y ⟨k, c⟩ ≠ 0 := ne_zero_of_pt y hz hc
    refine ⟨F c, ⟨n, F, c, ⟨hom, fun j j' => mul_right_cancel₀ yc ?_⟩, rfl⟩, hne⟩
    linear_combination y ⟨k, j'⟩ * rel j - y ⟨k, j⟩ * rel j'
  obtain ⟨T, hTS, hT'⟩ := exists_finset y k₀ hy S hS H
  have hch : ∀ f : T, ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ) (j : J k),
      Fam n F ∧ f.1 = F j := fun f => hTS f.2
  choose n F j hF hj using hch
  refine ⟨T.card, fun t => n (T.equivFin.symm t), fun t => F (T.equivFin.symm t),
    fun t => (hF _).1, fun t => (hF _).2, ?_⟩
  intro L _ _ z hz
  obtain ⟨f, hf, hne⟩ := hT' L z hz
  refine ⟨T.equivFin ⟨f, hf⟩, j ⟨f, hf⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [← hj ⟨f, hf⟩]
  exact hne

end GlobalTheory.CompanionTheory.Ar.FormFamilies
