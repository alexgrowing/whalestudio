import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MonomialCountAndBinomialEstimates
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.XSmulMemWeightedHomogeneousSubmodule
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IntegralStatementPfA

open Filter Module

namespace GlobalTheory

namespace ProjCut

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section Grading

variable {ι k : Type*} [Field k]

theorem isInternal_quotPiece {I : Ideal (MvPolynomial ι k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule ι k)) : DirectSum.IsInternal (quotPiece I) := by
  classical
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    rintro y ⟨a, ha, rfl⟩ hy
    have hmap : (⨆ (j) (_ : j ≠ i), quotPiece I j) =
        (⨆ (j) (_ : j ≠ i), weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) j).map
          (Ideal.Quotient.mkₐ k I).toLinearMap := by
      simp only [quotPiece, Submodule.map_iSup]
    rw [hmap] at hy
    obtain ⟨b, hb, hab⟩ := hy
    have hb0 : weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) i b = 0 := by
      have : (⨆ (j) (_ : j ≠ i), weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) j) ≤
          LinearMap.ker (weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) i) := by
        refine iSup₂_le fun j hj z hz => ?_
        rw [LinearMap.mem_ker, weightedHomogeneousComponent_of_mem hz, if_neg (Ne.symm hj)]
      exact this hb
    have hab' : a - b ∈ I := Ideal.Quotient.eq.mp hab.symm
    have h2 := weightedHomogeneousComponent_one_mem hI i hab'
    rw [map_sub, hb0, sub_zero, weightedHomogeneousComponent_of_mem ha, if_pos rfl] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h2
  · letI := weightedDecomposition k (fun _ : ι => (1 : ℤ))
    have htop := (DirectSum.Decomposition.isInternal
      (weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)))).submodule_iSup_eq_top
    unfold quotPiece
    rw [← Submodule.map_iSup, htop, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective k I)

theorem mk_mul_mem_quotPiece (I : Ideal (MvPolynomial ι k)) {z : MvPolynomial ι k}
    (hz : z.IsHomogeneous 1) (n : ℤ) {m : MvPolynomial ι k ⧸ I} (hm : m ∈ quotPiece I n) :
    Ideal.Quotient.mk I z * m ∈ quotPiece I (n + 1) := by
  obtain ⟨a, ha, rfl⟩ := hm
  have hz' : z ∈ weightedHomogeneousSubmodule k (fun _ : ι => (1 : ℤ)) ((1 : ℕ) : ℤ) := by
    rwa [weightedHomogeneousSubmodule_one_natCast]
  refine ⟨z * a, ?_, by simp⟩
  rw [add_comm]
  exact IsWeightedHomogeneous.mul hz' ha

theorem finrank_homogeneousSubmodule [Fintype ι] (n : ℕ) :
    finrank k (homogeneousSubmodule ι k n) = (n + Fintype.card ι - 1).choose n := by
  rw [← natCard_degree_eq, homogeneousSubmodule_eq_finsupp_supported]
  exact finrank_eq_nat_card_basis (basisRestrictSupport k _)

end Grading

section Projection

open ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

variable {ι k : Type*} [Field k]

theorem isIntegral_of_projection {σ R A : Type*} [Fintype σ] [CommRing R] [Algebra k R]
    [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
    (w : σ → A) (a : σ → R) (c : σ → k) (t : A)
    (h : ∀ j, w j = algebraMap k A (c j) * t + algebraMap R A (a j))
    {g : MvPolynomial σ k} {m : ℕ} (hg : g.IsHomogeneous m) (hw : aeval w g = 0)
    (hc : eval c g ≠ 0)
    (hint : (aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom.IsIntegral) :
    Algebra.IsIntegral R A := by
  classical
  let v : σ → Polynomial R := fun j =>
    Polynomial.C (algebraMap k R (c j)) * Polynomial.X + Polynomial.C (a j)
  let Q : Polynomial R := aeval v g
  have hv : ∀ i, (v i).natDegree ≤ 1 := fun i => Polynomial.natDegree_linear_le
  have hv1 : ∀ i, (v i).coeff 1 = algebraMap k R (c i) := by
    intro i
    simp [v, Polynomial.coeff_C]
  have hQe : Q = ∑ d ∈ g.support,
      Polynomial.C (algebraMap k R (g.coeff d)) * ∏ i, v i ^ d i := by
    simp only [Q, aeval_def, eval₂_eq']
    rfl
  have hdeg : ∀ d ∈ g.support, ∑ i, d i = m := by
    intro d hd
    have := hg (mem_support_iff.mp hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  have hQ1 : Q.natDegree ≤ m := by
    rw [hQe]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [← hdeg d hd]
    exact (prod_pow_natDegree_coeff' Finset.univ v d hv).1
  have hQ2 : Q.coeff m = algebraMap k R (eval c g) := by
    rw [hQe, Polynomial.finsetSum_coeff, eval_eq', map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Polynomial.coeff_C_mul, ← hdeg d hd, (prod_pow_natDegree_coeff' Finset.univ v d hv).2]
    simp [hv1]
  have hQ3 : Polynomial.aeval t Q = 0 := by
    have := comp_aeval_apply v ((Polynomial.aeval t : Polynomial R →ₐ[R] A).restrictScalars k) g
    simp only [AlgHom.restrictScalars_apply] at this
    rw [← hw, this]
    congr 2
    funext j
    simp [v, h j, ← IsScalarTower.algebraMap_apply]
  have ht : IsIntegral R t := by
    refine ⟨Polynomial.C (algebraMap k R (eval c g)⁻¹) * Q, ?_, ?_⟩
    · refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one m
        ((Polynomial.natDegree_C_mul_le _ _).trans hQ1) ?_
      rw [Polynomial.coeff_C_mul, hQ2, ← map_mul, inv_mul_cancel₀ hc, map_one]
    · rw [← Polynomial.aeval_def, map_mul, hQ3, mul_zero]
  let B := integralClosure R A
  have hk : ∀ x : k, algebraMap k A x ∈ B := fun x => by
    rw [IsScalarTower.algebraMap_apply k R A]; exact B.algebraMap_mem _
  have hB : ∀ p : MvPolynomial σ k, (aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom p ∈ B := by
    intro p
    change aeval w p ∈ B
    induction p using MvPolynomial.induction_on with
    | C x => rw [algHom_C]; exact hk x
    | add p q hp hq => rw [map_add]; exact B.add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, aeval_X, h]
      exact B.mul_mem hp (B.add_mem (B.mul_mem (hk _) ht) (B.algebraMap_mem _))
  have hB' : (algebraMap B A).IsIntegral :=
    RingHom.IsIntegral.tower_top
      ((aeval w : MvPolynomial σ k →ₐ[k] A).toRingHom.codRestrict B hB) (algebraMap B A) hint
  exact ⟨fun x => isIntegral_trans (A := B) x (hB' x)⟩

theorem homogeneousComponent_aeval {σ : Type*} (w : σ → MvPolynomial ι k)
    (hw : ∀ j, (w j).IsHomogeneous 1) (n : ℕ) (g : MvPolynomial σ k) :
    homogeneousComponent n (aeval w g) = aeval w (homogeneousComponent n g) := by
  classical
  induction g using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial d x =>
    have h1 : (monomial d x : MvPolynomial σ k).IsHomogeneous d.degree :=
      isHomogeneous_monomial x rfl
    have h2 := h1.aeval w hw
    rw [one_mul] at h2
    rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem h2]
    split_ifs <;> simp

theorem exists_linear_normalisation [Infinite k] {P : Ideal (MvPolynomial ι k)} (hP : P ≠ ⊤)
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (y : ι → k) (r : ℕ)
    (w : Fin r → MvPolynomial ι k) (hw : ∀ j, (w j).IsHomogeneous 1)
    (hy : ∀ j, eval y (w j) = 0)
    (hint : (aeval fun j => Ideal.Quotient.mk P (w j) :
      MvPolynomial (Fin r) k →ₐ[k] _).toRingHom.IsIntegral) :
    ∃ (s : ℕ) (z : Fin s → MvPolynomial ι k), (∀ j, (z j).IsHomogeneous 1) ∧
      (∀ j, eval y (z j) = 0) ∧
      (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _).toRingHom.IsIntegral ∧
      Function.Injective (aeval fun j => Ideal.Quotient.mk P (z j) :
        MvPolynomial (Fin s) k →ₐ[k] _) := by
  haveI : Nontrivial (MvPolynomial ι k ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  induction r with
  | zero =>
    refine ⟨0, w, hw, hy, hint, (injective_iff_map_eq_zero _).2 fun g hg => ?_⟩
    rw [eq_C_of_isEmpty g] at hg ⊢
    rw [algHom_C, map_eq_zero] at hg
    rw [hg, map_zero]
  | succ r ih =>
    by_cases hinj : Function.Injective (aeval fun j => Ideal.Quotient.mk P (w j) :
        MvPolynomial (Fin (r + 1)) k →ₐ[k] _)
    · exact ⟨r + 1, w, hw, hy, hint, hinj⟩
    rw [injective_iff_map_eq_zero] at hinj
    push Not at hinj
    obtain ⟨g, hg, hg0⟩ := hinj
    have e : ∀ g : MvPolynomial (Fin (r + 1)) k,
        aeval (fun j => Ideal.Quotient.mk P (w j)) g = Ideal.Quotient.mk P (aeval w g) :=
      fun g => (comp_aeval_apply w (Ideal.Quotient.mkₐ k P) g).symm
    obtain ⟨m, hm⟩ : ∃ m, homogeneousComponent m g ≠ 0 := by
      by_contra! hm
      apply hg0
      rw [← sum_homogeneousComponent g]
      exact Finset.sum_eq_zero fun m _ => hm m
    have hgm : aeval (fun j => Ideal.Quotient.mk P (w j)) (homogeneousComponent m g) = 0 := by
      rw [e, Ideal.Quotient.eq_zero_iff_mem] at hg ⊢
      rw [← homogeneousComponent_aeval w hw]
      exact homogeneousComponent_mem_of_mem hPh hg m
    obtain ⟨c, hc⟩ := exists_cons_one_ne (homogeneousComponent_isHomogeneous m g) hm
    let w' : Fin r → MvPolynomial ι k := fun j => w j.succ - C (c j) * w 0
    refine ih w' (fun j => (hw _).sub ((hw 0).C_mul _)) (fun j => by simp [w', hy]) ?_
    let φ : MvPolynomial (Fin r) k →ₐ[k] _ := aeval fun j => Ideal.Quotient.mk P (w' j)
    letI := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin r) k) (MvPolynomial ι k ⧸ P) :=
      IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    refine (isIntegral_of_projection (R := MvPolynomial (Fin r) k) _ (Fin.cons 0 X) (Fin.cons 1 c)
      (Ideal.Quotient.mk P (w 0)) ?_ (homogeneousComponent_isHomogeneous m g) hgm hc hint).1
    intro j
    refine Fin.cases (by simp) (fun j => ?_) j
    have : algebraMap (MvPolynomial (Fin r) k) (MvPolynomial ι k ⧸ P) (X j) =
        Ideal.Quotient.mk P (w' j) := aeval_X _ _
    simp only [Fin.cons_succ, this, w', map_sub, map_mul]
    rw [← algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    ring

end Projection

section Bound

variable {ι k : Type*} [Field k]

theorem hilbertPoly_ne_zero {P : Ideal (MvPolynomial ι k)} [P.IsPrime] (hne : ∃ i, X i ∉ P)
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece P) H) : H ≠ 0 := by
  rintro rfl
  obtain ⟨n, hn, hn0⟩ := (hH.eventually_eq.and (eventually_ge_atTop 0)).exists
  lift n to ℕ using hn0
  haveI := hH.finite n
  have hbot : quotPiece P (n : ℤ) = ⊥ := by simpa using hn
  obtain ⟨i, hi⟩ := hne
  have hmem : Ideal.Quotient.mk P (X i ^ n) ∈ quotPiece P (n : ℤ) := by
    rw [quotPiece_natCast]
    exact ⟨X i ^ n, isHomogeneous_X_pow i n, rfl⟩
  rw [hbot, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hi (Ideal.IsPrime.mem_of_pow_mem ‹_› n hmem)

theorem degree_lt_of_isIntegral {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ℳ : ℤ → Submodule k A) [DirectSum.Decomposition ℳ] {H : Polynomial ℚ}
    (hH : IsHilbertPoly ℳ H) {s : ℕ} (z : Fin s → A)
    (hz : ∀ j n, ∀ m ∈ ℳ n, z j * m ∈ ℳ (n + 1))
    (hint : (aeval z : MvPolynomial (Fin s) k →ₐ[k] A).toRingHom.IsIntegral) :
    H.degree < (s : ℕ) := by
  let φ : MvPolynomial (Fin s) k →ₐ[k] A := aeval z
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) A :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  haveI : Algebra.FiniteType (MvPolynomial (Fin s) k) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := Algebra.IsIntegral.finite
  obtain ⟨H', hH', hd⟩ := exists_isHilbertPoly (ι := Fin s) ℳ (fun j n m hm => by
    have : algebraMap (MvPolynomial (Fin s) k) A (X j) = z j := aeval_X _ _
    rw [Algebra.smul_def, this]
    exact hz j n m hm)
  rwa [hH'.unique hH, Fintype.card_fin] at hd

theorem exists_monic_minimal {R A : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] (φ : R →+* A) (hinj : Function.Injective φ) (hint : φ.IsIntegral)
    (t : A) : ∃ p : Polynomial R, p.Monic ∧ 0 < p.natDegree ∧ p.eval₂ φ t = 0 ∧
      ∀ a : Fin p.natDegree → R, ∑ j, φ (a j) * t ^ (j : ℕ) = 0 → a = 0 := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have ht : IsIntegral R t := hint t
  refine ⟨minpoly R t, minpoly.monic ht, minpoly.natDegree_pos ht, minpoly.aeval R t, ?_⟩
  intro a ha
  let q : Polynomial.degreeLT R (minpoly R t).natDegree := (Polynomial.degreeLTEquiv R _).symm a
  have hq : (q : Polynomial R) = ∑ j : Fin (minpoly R t).natDegree, Polynomial.monomial (j : ℕ) (a j) := rfl
  have hq0 : (q : Polynomial R) = 0 := by
    by_contra h0
    have h1 := minpoly.IsIntegrallyClosed.degree_le_of_ne_zero (s := t) h0 (by
      rw [hq, map_sum, ← ha]
      simp only [Polynomial.aeval_monomial]
      rfl)
    have h2 := Polynomial.mem_degreeLT.1 q.2
    rw [← Polynomial.degree_eq_natDegree (minpoly.ne_zero ht)] at h2
    exact h2.not_ge h1
  exact (LinearEquiv.map_eq_zero_iff _).1 (Subtype.ext hq0 : q = 0)

theorem mul_choose_le_finrank [Finite ι] (I : Ideal (MvPolynomial ι k)) {e d : ℕ}
    (z : Fin (e + 1) → MvPolynomial ι k) (hz : ∀ j, (z j).IsHomogeneous 1)
    {l : MvPolynomial ι k} (hl : l.IsHomogeneous 1)
    (hind : ∀ a : Fin d → MvPolynomial (Fin (e + 1)) k,
      ∑ j, aeval z (a j) * l ^ (j : ℕ) ∈ I → a = 0) (m : ℕ) :
    d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ)) := by
  rw [quotPiece_natCast]
  let L : (Fin d → homogeneousSubmodule (Fin (e + 1)) k m) →ₗ[k] MvPolynomial ι k :=
    ∑ j : Fin d, LinearMap.mulRight k (l ^ (j : ℕ)) ∘ₗ (aeval z).toLinearMap ∘ₗ
      LinearMap.mulRight k (X 0 ^ (d - j)) ∘ₗ (Submodule.subtype _) ∘ₗ LinearMap.proj j
  have hL : ∀ a, L a = ∑ j : Fin d, aeval z ((a j).1 * X 0 ^ (d - j)) * l ^ (j : ℕ) := by
    intro a
    simp only [L, LinearMap.sum_apply]
    rfl
  have hmem : ∀ a, ((Ideal.Quotient.mkₐ k I).toLinearMap ∘ₗ L) a ∈
      (homogeneousSubmodule ι k (m + d)).map (Ideal.Quotient.mkₐ k I).toLinearMap := by
    intro a
    refine ⟨L a, ?_, rfl⟩
    rw [hL]
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 : (a j).1.IsHomogeneous m := (a j).2
    have := ((h1.mul (isHomogeneous_X_pow 0 (d - j))).aeval z hz).mul (hl.pow j)
    have hj := j.2
    rwa [show 1 * (m + (d - j)) + 1 * (j : ℕ) = m + d by omega] at this
  have hinj : Function.Injective (LinearMap.codRestrict _ _ hmem) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : L a ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val ha)
    rw [hL] at h1
    have h2 := hind _ h1
    funext j
    exact Subtype.ext ((mul_eq_zero.1 (congrFun h2 j)).resolve_right (pow_ne_zero _ (X_ne_zero _)))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_pi_fintype, finrank_homogeneousSubmodule] at this
  simpa [← add_assoc, Nat.choose_symm_add] using this

theorem le_factorial_mul_leadingCoeff [Finite ι] {I : Ideal (MvPolynomial ι k)} {e d : ℕ}
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece I) H) (hdeg : H.degree ≤ (e : ℕ))
    (hd : 0 < d) (h : ∀ m, d * (m + e).choose e ≤ finrank k (quotPiece I ((m + d : ℕ) : ℤ))) :
    H.natDegree = e ∧ (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff := by
  have h1 : 0 ≤ (H - Polynomial.C (d : ℚ) * Polynomial.preHilbertPoly ℚ e d).coeff e := by
    apply coeff_nonneg_of_eventually_eval_nat
    · refine (Polynomial.degree_sub_le _ _).trans (max_le hdeg ?_)
      refine Polynomial.degree_le_of_natDegree_le ((Polynomial.natDegree_C_mul_le _ _).trans ?_)
      rw [Polynomial.natDegree_preHilbertPoly]
    · filter_upwards [tendsto_natCast_atTop_atTop.eventually hH.eventually_eq,
        eventually_ge_atTop d] with n hn hdn
      have := h (n - d)
      rw [Nat.sub_add_cancel hdn] at this
      rw [Int.cast_natCast] at hn
      rw [Polynomial.eval_sub, Polynomial.eval_C_mul,
        Polynomial.preHilbertPoly_eq_choose_sub_add _ _ hdn, ← hn, sub_nonneg]
      exact_mod_cast this
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_preHilbertPoly_self,
    sub_nonneg] at h1
  have hf : (0 : ℚ) < e.factorial := by exact_mod_cast e.factorial_pos
  have h2 : 0 < H.coeff e := lt_of_lt_of_le (by positivity) h1
  have h3 : H.natDegree = e :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (Polynomial.natDegree_le_of_degree_le hdeg) h2.ne'
  refine ⟨h3, ?_⟩
  rw [Polynomial.leadingCoeff, h3]
  rwa [← div_eq_mul_inv, div_le_iff₀' hf] at h1

theorem ringKrullDim_eq_natDegree_idealHilbertPoly [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P) :
    ringKrullDim (MvPolynomial ι k ⧸ P) = ((idealHilbertPoly P).natDegree + 1 : ℕ) := by
  classical
  cases nonempty_fintype ι
  have hH := isHilbertPoly_idealHilbertPoly hPh
  let ε := (Fintype.equivFin ι).symm
  obtain ⟨s, z, hz, -, hzint, hzinj⟩ := exists_linear_normalisation
    (Ideal.IsPrime.ne_top ‹_›) hPh 0 _ (fun j => X (ε j))
    (fun j => isHomogeneous_X _ _) (fun j => by simp) (by
      refine RingHom.isIntegral_of_surjective _ fun x => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨rename ε.symm x, ?_⟩
      have : (aeval fun j => Ideal.Quotient.mk P (X (ε j)) :
          MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _).comp (rename ε.symm) =
          Ideal.Quotient.mkₐ k P := by
        ext j; simp
      exact DFunLike.congr_fun this x)
  letI := (isInternal_quotPiece hPh).chooseDecomposition
  have hdeg := degree_lt_of_isIntegral (quotPiece P) hH _
    (fun j n m hm => mk_mul_mem_quotPiece P (hz j) n hm) hzint
  obtain _ | e := s
  · exfalso
    exact hilbertPoly_ne_zero hne hH (by simpa using hdeg)
  have hdeg' : (idealHilbertPoly P).degree ≤ (e : ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hdeg.trans_le (by exact_mod_cast (by exact_mod_cast hn : e < n)))
  obtain ⟨i, -⟩ := hne
  have he := (le_factorial_mul_leadingCoeff hH hdeg' one_pos
    (mul_choose_le_finrank P z hz (isHomogeneous_X k i) (fun a ha => by
      funext j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      refine (injective_iff_map_eq_zero _).1 hzinj _ ?_
      refine (comp_aeval_apply z (Ideal.Quotient.mkₐ k P) _).symm.trans ?_
      simpa [Ideal.Quotient.eq_zero_iff_mem] using ha))).1
  let φ : MvPolynomial (Fin (e + 1)) k →ₐ[k] _ := aeval fun j => Ideal.Quotient.mk P (z j)
  letI := φ.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin (e + 1)) k) (MvPolynomial ι k ⧸ P) := ⟨hzint⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective
    (A := MvPolynomial (Fin (e + 1)) k) hzinj, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, he]
  simp

end Bound

end ProjCut

open MvPolynomial ProjCut ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι k : Type*} [Field k]

theorem exists_form_degree_le_of_isHilbertPoly [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P)
    {H : Polynomial ℚ} (hH : IsHilbertPoly (quotPiece P) H)
    (y : ι → k) (hy : ∃ f ∈ P, eval y f ≠ 0) :
    ∃ (d : ℕ) (f : MvPolynomial ι k), f ∈ P ∧ f.IsHomogeneous d ∧
      (d : ℚ) ≤ H.natDegree.factorial * H.leadingCoeff ∧ eval y f ≠ 0 := by
  classical
  cases nonempty_fintype ι
  have hP : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨g, hgP, hg⟩ := hy
  obtain ⟨m, hm⟩ : ∃ m, eval y (homogeneousComponent m g) ≠ 0 := by
    by_contra! hm
    apply hg
    rw [← sum_homogeneousComponent g, map_sum]
    exact Finset.sum_eq_zero fun m _ => hm m
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! h0
    obtain rfl : y = 0 := funext h0
    have h1 := homogeneousComponent_mem_of_mem hPh hgP 0
    rw [homogeneousComponent_zero] at h1
    rw [eval_zero, constantCoeff_eq] at hg
    exact hP (P.eq_top_of_isUnit_mem h1 (hg.isUnit.map C))

  let ε := (Fintype.equivFin ι).symm
  let w : Fin (Fintype.card ι) → MvPolynomial ι k := fun j => X (ε j) - C (y (ε j) / y i) * X i
  have hint : (aeval fun j => Ideal.Quotient.mk P (w j) :
      MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _).toRingHom.IsIntegral := by
    let φ : MvPolynomial (Fin (Fintype.card ι)) k →ₐ[k] _ :=
      aeval fun j => Ideal.Quotient.mk P (w j)
    letI := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k (MvPolynomial (Fin (Fintype.card ι)) k) (MvPolynomial ι k ⧸ P) :=
      IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
    have e : (aeval fun j => Ideal.Quotient.mk P (X j) : MvPolynomial ι k →ₐ[k] _) =
        Ideal.Quotient.mkₐ k P := by
      ext j; simp
    refine (isIntegral_of_projection (R := MvPolynomial (Fin (Fintype.card ι)) k)
      (fun j => Ideal.Quotient.mk P (X j)) (fun j => X (ε.symm j)) y
      (Ideal.Quotient.mk P (C (y i)⁻¹ * X i)) ?_ (homogeneousComponent_isHomogeneous m g) ?_ hm
      ?_).1
    · intro j
      have : algebraMap (MvPolynomial (Fin (Fintype.card ι)) k) (MvPolynomial ι k ⧸ P)
          (X (ε.symm j)) = Ideal.Quotient.mk P (w (ε.symm j)) := aeval_X _ _
      rw [this, ← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_add]
      congr 1
      simp only [w, Equiv.apply_symm_apply, div_eq_mul_inv, map_mul, algebraMap_eq]
      ring
    · rw [e]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (homogeneousComponent_mem_of_mem hPh hgP m)
    · rw [e]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective k P)
  obtain ⟨s, z, hz, hzy, hzint, hzinj⟩ := exists_linear_normalisation hP hPh y _ w
    (fun j => (isHomogeneous_X _ _).sub ((isHomogeneous_X _ _).C_mul _))
    (fun j => by simp [w, hi]) hint
  letI := (isInternal_quotPiece hPh).chooseDecomposition
  have hdeg := degree_lt_of_isIntegral (quotPiece P) hH _
    (fun j n m hm => mk_mul_mem_quotPiece P (hz j) n hm) hzint
  obtain _ | e := s
  · exfalso
    exact hilbertPoly_ne_zero hne hH (by simpa using hdeg)
  have hdeg' : H.degree ≤ (e : ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    exact Polynomial.coeff_eq_zero_of_degree_lt
      (hdeg.trans_le (by exact_mod_cast (by exact_mod_cast hn : e < n)))
  obtain ⟨p, hp, hp0, hpt, hind⟩ := exists_monic_minimal _ hzinj hzint (Ideal.Quotient.mk P (X i))
  have e1 : ∀ a : MvPolynomial (Fin (e + 1)) k,
      aeval (fun j => Ideal.Quotient.mk P (z j)) a = Ideal.Quotient.mk P (aeval z a) :=
    fun a => (comp_aeval_apply z (Ideal.Quotient.mkₐ k P) a).symm
  have hle := (le_factorial_mul_leadingCoeff hH hdeg' hp0
    (mul_choose_le_finrank P z hz (isHomogeneous_X k i) (fun a ha => hind a (by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum] at ha
      rw [← ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, ← e1]
      rfl)))).2
  let F : MvPolynomial ι k := p.eval₂ (aeval z : MvPolynomial (Fin (e + 1)) k →ₐ[k] _).toRingHom (X i)
  have hF : F ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂, ← hpt]
    congr 1
    exact RingHom.ext fun a => (e1 a).symm
  refine ⟨p.natDegree, homogeneousComponent p.natDegree F,
    homogeneousComponent_mem_of_mem hPh hF _, homogeneousComponent_isHomogeneous _ _, hle, ?_⟩
  have h1 := coeff_cone (R := k) y F p.natDegree
  have h2 : cone (R := k) y F =
      (p.map constantCoeff).comp (Polynomial.C (y i) * Polynomial.X) := by
    have h3 := Polynomial.hom_eval₂ p
      (aeval z : MvPolynomial (Fin (e + 1)) k →ₐ[k] _).toRingHom (cone (R := k) y).toRingHom (X i)
    rw [Polynomial.comp, Polynomial.eval₂_map]
    refine h3.trans ?_
    congr 1
    · ext a : 1
      · ext a : 1
        simp
      · have := cone_homog (R := k) y (hz a)
        simp [this, hzy]
    · simp [cone]
  rw [h2, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map, hp.coeff_natDegree, map_one,
    one_mul] at h1
  rw [← coe_aeval_eq_eval]
  exact h1 ▸ pow_ne_zero _ hi

theorem exists_form_degree_le_hilbertDegree_eval_ne_zero [Infinite k] [Finite ι]
    {P : Ideal (MvPolynomial ι k)} [P.IsPrime]
    (hPh : P.IsHomogeneous (homogeneousSubmodule ι k)) (hne : ∃ i, X i ∉ P)
    (y : ι → k) (hy : ∃ f ∈ P, eval y f ≠ 0) :
    ∃ d ≤ hilbertDegree P, ∃ f ∈ P, f.IsHomogeneous d ∧ eval y f ≠ 0 := by
  obtain ⟨d, f, hf, hfd, hd, hy⟩ := exists_form_degree_le_of_isHilbertPoly hPh hne
    (isHilbertPoly_idealHilbertPoly hPh) y hy
  rw [← cast_hilbertDegree hPh] at hd
  exact ⟨d, by exact_mod_cast hd, f, hf, hfd, hy⟩

end GlobalTheory
