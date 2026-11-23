import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightSubringPrimeMaximal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem exists_isWeightedHomogeneous_eq_of_chart {R : Type*} [CommRing R]
    (χ : MvPolynomial (Coord n) ℤ →+* R) (c : (k : ι) → Fin (n k + 1))
    (hχ : ∀ k, χ (X ⟨k, c k⟩) = 1) (g : MvPolynomial (Coord n) ℤ) :
    ∃ (D : ι → ℕ) (G : MvPolynomial (Coord n) ℤ),
      IsWeightedHomogeneous (coordDeg n) G D ∧ χ G = χ g := by
  have hmon : ∀ e, χ (chartMonomial c e) = 1 := fun e ↦ by
    simp [chartMonomial, map_prod, hχ]
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isWeightedHomogeneous_C _ _, rfl⟩
  | add p q hp hq =>
    obtain ⟨D₁, G₁, h₁, e₁⟩ := hp
    obtain ⟨D₂, G₂, h₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, G₁ * chartMonomial c D₂ + G₂ * chartMonomial c D₁, ?_, ?_⟩
    · refine IsWeightedHomogeneous.add (h₁.mul (isWeightedHomogeneous_chartMonomial c D₂)) ?_
      rw [add_comm D₁]
      exact h₂.mul (isWeightedHomogeneous_chartMonomial c D₁)
    · rw [map_add, map_mul, map_mul, hmon, hmon, mul_one, mul_one, e₁, e₂, map_add]
  | mul_X p i hp =>
    obtain ⟨D, G, h, e⟩ := hp
    exact ⟨D + coordDeg n i, G * X i, h.mul (isWeightedHomogeneous_X ℤ _ i),
      by rw [map_mul, map_mul, e]⟩

theorem aeval_div_chart {Ω : Type*} [Field Ω] [Algebra ℤ Ω] (z : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (G : MvPolynomial (Coord n) ℤ) (d : ι → ℕ) (hG : IsWeightedHomogeneous (coordDeg n) G d) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) G = aeval z G * ∏ k, (z ⟨k, c k⟩ ^ d k)⁻¹ := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmd : ∀ k, ∑ i, m ⟨k, i⟩ = d k := (geoMultiHomog_iff G d).mpr hG m hm
  rw [mul_assoc]
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  have hden : ∏ p : Coord n, z ⟨p.1, c p.1⟩ ^ m p = ∏ k, z ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [← hmd k, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, hden, div_eq_mul_inv, Finset.prod_inv_distrib]

omit [DecidableEq ι] in

theorem mem_orbitIdeal_iff_of_isMultiHomog (x : Cone n (AlgebraicClosure ℚ))
    (F : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hF : Geo.IsMultiHomog (ι := blockIdx n) F a) :
    F ∈ orbitIdeal x ↔ evalCone (coordVec x) F = 0 := by
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) F =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) F) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ F a hF, e,
    mul_eq_zero, C_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero k))

omit [DecidableEq ι] in

theorem exists_chart_ciSup (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (v : FinitePlace (coordField x)) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, v (coordVec x k (c k)) = ⨆ i, v (coordVec x k i) ∧
      0 < ⨆ i, v (coordVec x k i) := by
  choose c hc using fun k ↦ exists_eq_ciSup_of_finite (f := fun i ↦ v (coordVec x k i))
  refine ⟨c, fun k ↦ ⟨hc k, ?_⟩⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
  have hi' : coordVec x k i ≠ 0 := fun h ↦ hi (congrArg Subtype.val h)
  exact (FinitePlace.pos_iff.mpr hi').trans_le
    (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Set.finite_range _).bddAbove i)

theorem finitePlace_aeval_le_one {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
    {σ : Type*} (y : σ → K) (hy : ∀ p, v (y p) ≤ 1) (g : MvPolynomial σ ℤ) :
    v (aeval y g) ≤ 1 := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact IsNonarchimedean.apply_intCast_le_one (fun a b ↦ FinitePlace.add_le v a b)
  | add p q hp hq =>
    rw [map_add]
    exact (FinitePlace.add_le v _ _).trans (max_le hp hq)
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X]
    exact mul_le_one₀ hp (apply_nonneg v _) (hy i)

theorem orbitCenter_le_of_le (hMI : OrbitCenterMemIff.Statement)
    (hSP : SubringPrimeMaximal.Statement) (x : Cone n (AlgebraicClosure ℚ)) (hx : BlockNonzero x)
    (v : FinitePlace (coordField x)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, v (coordVec x k (c k)) = ⨆ i, v (coordVec x k i) ∧ 0 < ⨆ i, v (coordVec x k i))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hsW : s ∉ orbitIdeal x) (Q : Ideal (MvPolynomial (Coord n) ℤ)) [hQp : Q.IsPrime]
    (hWQ : orbitIdeal x ≤ Q) (hsQ : s ∈ Q) (hQv : Q ≤ orbitCenter x v) :
    orbitCenter x v ≤ Q := by
  set xv := coordVec x
  set M : ι → ℝ := fun k ↦ ⨆ i, v (xv k i)
  have hxc : ∀ k, xv k (c k) ≠ 0 := fun k ↦ FinitePlace.pos_iff.mp ((hc k).1 ▸ (hc k).2)
  have hPpos : ∀ d : ι → ℕ, 0 < ∏ k, M k ^ d k := fun d ↦
    Finset.prod_pos fun k _ ↦ pow_pos (hc k).2 _

  let φ : MvPolynomial (Coord n) ℤ →ₐ[ℤ] coordField x :=
    aeval fun p ↦ xv p.1 p.2 / xv p.1 (c p.1)
  have hφ : ∀ G d, IsWeightedHomogeneous (coordDeg n) G d →
      φ G = evalCone xv G * ∏ k, (xv k (c k) ^ d k)⁻¹ := fun G d hG ↦ by
    refine (aeval_div_chart (fun q : Coord n ↦ xv q.1 q.2) c G d hG).trans ?_
    rw [aeval_def, evalCone, Subsingleton.elim (algebraMap ℤ (coordField x)) (Int.castRingHom _)]
  have hprod : ∀ d : ι → ℕ, ∏ k, (xv k (c k) ^ d k)⁻¹ ≠ 0 := fun d ↦
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hxc k))
  have hφv : ∀ G d, IsWeightedHomogeneous (coordDeg n) G d →
      (v (φ G) < 1 ↔ v (evalCone xv G) < ∏ k, M k ^ d k) := fun G d hG ↦ by
    rw [hφ G d hG, map_mul, map_prod]
    simp_rw [map_inv₀, map_pow, (hc _).1]
    rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, div_lt_one (hPpos d)]

  let π : MvPolynomial (Coord n) ℤ →+* FractionRing (MvPolynomial (Coord n) ℤ ⧸ Q) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ G, π G = 0 ↔ G ∈ Q := fun G ↦ by
    rw [RingHom.comp_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _),
      Ideal.Quotient.eq_zero_iff_mem]
  have hXc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ Q := fun k h ↦ by
    have := (hMI ι n x hx v _ _ ((geoMultiHomog_iff _ _).mpr
      (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩))).mp (hQv h)
    simp [evalCone, coordDeg, Pi.single_apply, pow_ite, xv, (hc k).1] at this
  let w : Coord n → FractionRing (MvPolynomial (Coord n) ℤ ⧸ Q) := fun p ↦ π (X p)
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k h ↦ hXc k ((hπ _).mp h)
  let ψ : MvPolynomial (Coord n) ℤ →ₐ[ℤ] FractionRing (MvPolynomial (Coord n) ℤ ⧸ Q) :=
    aeval fun p ↦ w p / w ⟨p.1, c p.1⟩
  have hπa : ∀ G, aeval w G = π G := fun G ↦ by
    have h : (aeval w : MvPolynomial (Coord n) ℤ →ₐ[ℤ] _).toRingHom = π :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p ↦ by simp [w]
    exact DFunLike.congr_fun h G
  have hψ : ∀ G d, IsWeightedHomogeneous (coordDeg n) G d → (ψ G = 0 ↔ G ∈ Q) := fun G d hG ↦ by
    rw [show ψ G = aeval w G * ∏ k, (w ⟨k, c k⟩ ^ d k)⁻¹ from aeval_div_chart w c G d hG, hπa, mul_eq_zero, hπ,
      or_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ ↦ inv_ne_zero (pow_ne_zero _ (hwc k)))]

  have hhom : ∀ g, ∃ D G, IsWeightedHomogeneous (coordDeg n) G D ∧ φ G = φ g ∧ ψ G = ψ g :=
    fun g ↦ by
      obtain ⟨D, G, hG, e⟩ := exists_isWeightedHomogeneous_eq_of_chart
        (R := coordField x × FractionRing (MvPolynomial (Coord n) ℤ ⧸ Q))
        ((φ : MvPolynomial (Coord n) ℤ →+* coordField x).prod
          (ψ : MvPolynomial (Coord n) ℤ →+* FractionRing (MvPolynomial (Coord n) ℤ ⧸ Q))) c
        (fun k ↦ by
          rw [RingHom.prod_apply]
          exact Prod.ext (by simp [φ, div_self (hxc k)]) (by simp [ψ, div_self (hwc k)])) g
      exact ⟨D, G, hG, congrArg Prod.fst e, congrArg Prod.snd e⟩
  let φ' := φ.rangeRestrict
  have hφ' : ∀ g, (φ' g : coordField x) = φ g := fun _ ↦ rfl
  have hker : RingHom.ker φ' ≤ RingHom.ker ψ := fun g hg ↦ by
    obtain ⟨D, G, hG, e₁, e₂⟩ := hhom g
    have h0 : φ g = 0 := by rw [← hφ' g, (RingHom.mem_ker).mp hg]; rfl
    rw [RingHom.mem_ker, ← e₂, hψ G D hG]
    refine hWQ ((mem_orbitIdeal_iff_of_isMultiHomog x G D ((geoMultiHomog_iff _ _).mpr hG)).mpr ?_)
    rw [← e₁, hφ G D hG] at h0
    exact (mul_eq_zero.mp h0).resolve_right (hprod D)
  have hsa := (geoMultiHomog_iff s a).mp hs
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  let q : Ideal φ.range := Ideal.map φ' (RingHom.ker ψ)
  have hqp : q.IsPrime := Ideal.map_isPrime_of_surjective (AlgHom.rangeRestrict_surjective φ) hker
  have hqne : q ≠ ⊥ := fun h ↦ by
    have hm : φ' s ∈ q := Ideal.mem_map_of_mem _ ((RingHom.mem_ker).mpr ((hψ s a hsa).mpr hsQ))
    rw [h, Ideal.mem_bot] at hm
    have h1 := congrArg Subtype.val hm
    rw [hφ', hφ s a hsa] at h1
    exact mul_ne_zero (evalCone_coordVec_ne_zero x s a hs hsW) (hprod a) h1
  have hqm := hSP _ φ.range q hqp hqne
  have hq1 : ∀ b ∈ q, v (b : coordField x) < 1 := fun b hb ↦ by
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (AlgHom.rangeRestrict_surjective φ)).mp hb
    obtain ⟨D, G, hG, e₁, e₂⟩ := hhom g
    rw [hφ', ← e₁, hφv G D hG]
    rw [RingHom.mem_ker, ← e₂, hψ G D hG] at hg
    exact (hMI ι n x hx v G D ((geoMultiHomog_iff _ _).mpr hG)).mp (hQv hg)
  have hle1 : ∀ g, v (φ g) ≤ 1 := finitePlace_aeval_le_one v _ fun p ↦ by
    rw [map_div₀, div_le_one (((hc p.1).1).symm ▸ (hc p.1).2), (hc p.1).1]
    exact le_ciSup (f := fun i ↦ v (xv p.1 i)) (Set.finite_range _).bddAbove p.2
  have hinq : ∀ b : φ.range, v (b : coordField x) < 1 → b ∈ q := fun b hb ↦ by
    by_contra hnb
    obtain ⟨u, i, hi, h1⟩ := hqm.exists_inv hnb
    obtain ⟨g, hg⟩ := AlgHom.rangeRestrict_surjective φ u
    have h1' : v ((u : coordField x) * b + i) = 1 := by
      rw [show (u : coordField x) * b + i = ((u * b + i : φ.range) : coordField x) from rfl, h1]
      exact map_one v
    have hu : v (u : coordField x) ≤ 1 := by rw [← hg, hφ']; exact hle1 g
    have := (FinitePlace.add_le v _ _).trans_lt (max_lt (by
      rw [map_mul]; exact (mul_le_of_le_one_left (apply_nonneg v _) hu).trans_lt hb) (hq1 i hi))
    exact absurd h1' this.ne
  refine Ideal.span_le.mpr fun F ⟨d, hFd, hlt⟩ ↦ ?_
  have hFw := (geoMultiHomog_iff F d).mp hFd
  obtain ⟨g, hg, e⟩ := (Ideal.mem_map_iff_of_surjective _ (AlgHom.rangeRestrict_surjective φ)).mp
    (hinq (φ' F) ((hφv F d hFw).mpr hlt))
  have hFg : F - g ∈ RingHom.ker ψ := hker ((RingHom.mem_ker).mpr (by rw [map_sub, e, sub_self]))
  rw [RingHom.mem_ker, map_sub, (RingHom.mem_ker).mp hg, sub_zero] at hFg
  exact (hψ F d hFw).mp hFg

end GroundTheory.Heights₂.Heights
