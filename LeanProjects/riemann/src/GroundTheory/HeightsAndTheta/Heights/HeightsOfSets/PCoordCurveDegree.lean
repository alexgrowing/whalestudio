import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4

namespace CoordCurveDegree

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

def blockDeg (m : (Σ k, ι k) →₀ ℕ) (k : K) : ℕ := ∑ i, m ⟨k, i⟩

def homog (d : ∀ k, ι k) (N : ℕ) (g : MvPolynomial (Σ k, ι k) ℚ) : MvPolynomial (Σ k, ι k) ℚ :=
  ∑ m ∈ g.support, monomial m (coeff m g) * ∏ k, X ⟨k, d k⟩ ^ (N - blockDeg m k)

theorem blockDeg_le_totalDegree {R : Type*} [CommSemiring R] {g : MvPolynomial (Σ k, ι k) R}
    {m : (Σ k, ι k) →₀ ℕ} (hm : m ∈ g.support) (k : K) : blockDeg m k ≤ g.totalDegree := by
  refine le_trans ?_ (le_totalDegree hm)
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl), Fintype.sum_sigma]
  exact Finset.single_le_sum (f := fun k ↦ ∑ i, m ⟨k, i⟩) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)

theorem eval₂_homog {L : Type*} [Field L] (f : ℚ →+* L) (d : ∀ k, ι k) (N : ℕ)
    (g : MvPolynomial (Σ k, ι k) ℚ) (hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ N)
    (w : (Σ k, ι k) → L) (hw : ∀ k, w ⟨k, d k⟩ ≠ 0) :
    eval₂ f w (homog d N g) = (∏ k, w ⟨k, d k⟩ ^ N) * eval₂ f (fun p ↦ w p / w ⟨p.1, d p.1⟩) g := by
  conv_rhs => rw [g.as_sum]
  rw [homog, eval₂_sum, eval₂_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [eval₂_mul, eval₂_monomial, eval₂_monomial, eval₂_prod]
  simp only [eval₂_pow, eval₂_X, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  have h1 : ∏ p, (w p / w ⟨p.1, d p.1⟩) ^ m p =
      (∏ p, w p ^ m p) / ∏ k, w ⟨k, d k⟩ ^ blockDeg m k := by
    simp only [div_pow, Finset.prod_div_distrib, blockDeg]
    congr 1
    rw [Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun k _ ↦ Finset.prod_pow_eq_pow_sum (s := Finset.univ)
      (f := fun i ↦ m ⟨k, i⟩) (a := w ⟨k, d k⟩)
  have h2 : ∏ k, w ⟨k, d k⟩ ^ N =
      (∏ k, w ⟨k, d k⟩ ^ (N - blockDeg m k)) * ∏ k, w ⟨k, d k⟩ ^ blockDeg m k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ ↦ by rw [← pow_add, Nat.sub_add_cancel (hN m hm k)]
  have h3 : ∏ k, w ⟨k, d k⟩ ^ blockDeg m k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hw k)
  rw [h1, h2]
  field_simp

theorem ratio_mem (y : (Σ k, ι k) → Ω) {p q : Σ k, ι k} (h : p.1 = q.1) : y p / y q ∈ blockFnField y :=
  IntermediateField.subset_adjoin _ _ ⟨p, q, h, rfl⟩

theorem blockFnField_eq (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    blockFnField y =
      IntermediateField.adjoin ℚ (Set.range fun p : Σ k, ι k ↦ y p / y ⟨p.1, d p.1⟩) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro t ⟨p, q, hpq, rfl⟩
    have e : y p / y q = (y p / y ⟨p.1, d p.1⟩) / (y q / y ⟨q.1, d q.1⟩) := by
      rw [hpq, div_div_div_cancel_right₀ (hd q.1)]
    rw [e]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
  · rintro t ⟨p, rfl⟩
    exact ratio_mem y rfl

def ratioF (y : (Σ k, ι k) → Ω) (d : ∀ k, ι k) (p : Σ k, ι k) : blockFnField y :=
  ⟨y p / y ⟨p.1, d p.1⟩, ratio_mem y rfl⟩

theorem eval₂_ratio_eq_zero {y : (Σ k, ι k) → Ω} (d : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    eval₂ (Int.castRingHom Ω) (fun p ↦ y p / y ⟨p.1, d p.1⟩) f = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_def] at hf
  have h2 := congrArg (MvPolynomial.eval fun k ↦ (y ⟨k, d k⟩)⁻¹) hf
  rw [eval₂_comp_left, map_zero] at h2
  convert h2 using 2
  · exact RingHom.ext_int _ _
  · funext p
    simp [div_eq_mul_inv]

theorem eval₂_ratioF_eq_zero {y : (Σ k, ι k) → Ω} (d : ∀ k, ι k) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    eval₂ (Int.castRingHom _) (ratioF y d) f = 0 := by
  apply (algebraMap (blockFnField y) Ω).injective
  rw [map_zero, eval₂_comp_left]
  convert eval₂_ratio_eq_zero d hf using 2
  · exact RingHom.ext_int _ _
  · rfl

def ptOf (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (φ : blockFnField y →ₐ[ℚ] ℂ) : (Σ k, ι k) → ℂ :=
  fun p ↦ φ (ratioF y c p)

theorem ptOf_chart {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (φ : blockFnField y →ₐ[ℚ] ℂ) (k : K) : ptOf y c φ ⟨k, c k⟩ = 1 := by
  have : ratioF y c ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
  rw [ptOf, this, map_one]

theorem ptOf_mem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (φ : blockFnField y →ₐ[ℚ] ℂ) : ptOf y c φ ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k ↦ ⟨c k, by rw [ptOf_chart hc]; exact one_ne_zero⟩, fun f hf ↦ ?_⟩
  rw [eval_map]
  have := congrArg (φ : blockFnField y →+* ℂ) (eval₂_ratioF_eq_zero c hf)
  rw [map_zero, eval₂_comp_left] at this
  convert this using 2
  · exact RingHom.ext_int _ _
  · rfl

theorem scale_equivalence (W : Ideal (MRing ι)) :
    Equivalence (fun z z' : mcPts W ↦ ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (z' : (Σ k, ι k) → ℂ) = fun p ↦ c p.1 * (z : (Σ k, ι k) → ℂ) p) := by
  refine ⟨fun z ↦ ⟨1, fun _ ↦ one_ne_zero, by funext p; simp⟩, ?_, ?_⟩
  · rintro z z' ⟨c, hc, h⟩
    refine ⟨c⁻¹, fun k ↦ inv_ne_zero (hc k), funext fun p ↦ ?_⟩
    rw [h]
    simp [inv_mul_cancel_left₀ (hc p.1)]
  · rintro z z' z'' ⟨c, hc, h⟩ ⟨c', hc', h'⟩
    refine ⟨c' * c, fun k ↦ mul_ne_zero (hc' k) (hc k), funext fun p ↦ ?_⟩
    rw [h', h]
    simp [mul_assoc]

theorem aeval_pt_eq_zero {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (d : ∀ k, ι k)
    (hyd : ∀ k, y ⟨k, d k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hd : ∀ k, z ⟨k, d k⟩ ≠ 0) {g : MvPolynomial (Σ k, ι k) ℚ}
    (hg0 : aeval (fun p ↦ y p / y ⟨p.1, d p.1⟩) g = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g = 0 := by
  have hN : ∀ m ∈ g.support, ∀ k, blockDeg m k ≤ g.totalDegree := fun m hm k ↦
    blockDeg_le_totalDegree hm k

  have hG : homog d g.totalDegree g ∈ RingHom.ker (coneMapQ y) := by
    rw [RingHom.mem_ker]
    let j := algebraMap (MvPolynomial K Ω) (FractionRing (MvPolynomial K Ω))
    have hj : Function.Injective j := IsFractionRing.injective _ _
    apply hj
    have hw : ∀ k, (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) ⟨k, d k⟩ ≠ 0 := fun k ↦
      (map_ne_zero_iff j hj).mpr (mul_ne_zero (C_ne_zero.mpr (hyd k)) (X_ne_zero _))
    rw [map_zero, coneMapQ, aeval_def, eval₂_comp_left, eval₂_homog _ d _ g hN _ hw]
    apply mul_eq_zero_of_right
    have e : (fun p : Σ k, ι k ↦ (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) p /
        (j ∘ fun p : Σ k, ι k ↦ C (y p) * X p.1) ⟨p.1, d p.1⟩) =
        (j.comp C) ∘ fun p ↦ y p / y ⟨p.1, d p.1⟩ := by
      funext p
      have hX : j (X p.1) ≠ 0 := (map_ne_zero_iff j hj).mpr (X_ne_zero _)
      simp only [Function.comp_apply, map_mul, RingHom.coe_comp]
      rw [mul_div_mul_right _ _ hX, ← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.comp_apply,
        map_div₀]
    rw [e, show j.comp (algebraMap ℚ (MvPolynomial K Ω)) = (j.comp C).comp (algebraMap ℚ Ω) from
      RingHom.ext_rat _ _, ← eval₂_comp_left, ← aeval_def, hg0, map_zero]

  have hGz : aeval z (homog d g.totalDegree g) = 0 := by
    rw [ker_coneMapQ hP] at hG
    have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤
        RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def]
      have := hz.2 f hf
      rw [eval_map] at this
      convert this using 2
      exact RingHom.ext_int _ _
    exact hle hG
  rw [aeval_def, eval₂_homog _ d _ g hN _ hd] at hGz
  rw [aeval_def]
  exact (mul_eq_zero.mp hGz).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hd k))

theorem exists_ptOf {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) {c : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    ∃ φ : blockFnField y →ₐ[ℚ] ℂ, ptOf y c φ = (fun p ↦ (z ⟨p.1, c p.1⟩)⁻¹ * z p) ∧
      ∀ k, z ⟨k, c k⟩ ≠ 0 := by
  have halg := isAlgebraic_blockFnField hP
  choose d hd using hz.1
  have hyd : ∀ k, y ⟨k, d k⟩ ≠ 0 := fun k h ↦ hd k (by simpa using hz.2 _ (X_mem_of_eq_zero h))
  let ev : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] blockFnField y := aeval (ratioF y d)
  have hval : ∀ g, ((ev g : blockFnField y) : Ω) = aeval (fun p ↦ y p / y ⟨p.1, d p.1⟩) g :=
    fun g ↦ comp_aeval_apply (f := ratioF y d) (blockFnField y).val g
  have hsurj : Function.Surjective ev := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin ℚ (Set.range fun p ↦ y p / y ⟨p.1, d p.1⟩) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic, ← blockFnField_eq y d hyd]
      · exact x.2
      · rintro _ ⟨p, rfl⟩
        exact IntermediateField.isAlgebraic_iff.mp (halg.isAlgebraic (ratioF y d p))
    rw [Algebra.adjoin_range_eq_range_aeval] at hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, Subtype.ext ((hval g).trans hg)⟩
  have hker : ∀ g ∈ RingHom.ker ev, aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g = 0 := fun g hg ↦
    aeval_pt_eq_zero hP d hyd hz hd (by rw [← hval, RingHom.mem_ker.mp hg]; rfl)
  let φ : blockFnField y →ₐ[ℚ] ℂ :=
    (Ideal.Quotient.liftₐ (RingHom.ker ev) (aeval fun p ↦ z p / z ⟨p.1, d p.1⟩) hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hφ : ∀ g, φ (ev g) = aeval (fun p ↦ z p / z ⟨p.1, d p.1⟩) g := fun g ↦ by
    have : (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (ev g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker ev) _ hker)
      ((Ideal.quotientKerAlgEquivOfSurjective hsurj).symm (ev g)) = _
    rw [this]
    rfl
  have hpt : ∀ p, ptOf y c φ p = z p / z ⟨p.1, c p.1⟩ := fun p ↦ by
    have e : ratioF y c p = ev (X p) / ev (X ⟨p.1, c p.1⟩) := by
      apply Subtype.ext
      simp only [ev, aeval_X, ratioF, IntermediateField.coe_div]
      exact (div_div_div_cancel_right₀ (hyd p.1) _ _).symm
    rw [ptOf, e, map_div₀, hφ, hφ, aeval_X, aeval_X]
    exact div_div_div_cancel_right₀ (hd p.1) _ _
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h ↦ by
    have := ptOf_chart hc φ k
    rw [hpt, h, div_zero] at this
    exact zero_ne_one this
  exact ⟨φ, funext fun p ↦ by rw [hpt, div_eq_inv_mul], hzc⟩

theorem degC_eq {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Nat.card (blockFnField y →ₐ[ℚ] ℂ) := by
  choose c hc0 using hP.2.1.2.2
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h ↦ hc0 k (X_mem_of_eq_zero h)
  unfold degC
  refine (Nat.card_eq_of_bijective (fun φ ↦ Quot.mk _ ⟨ptOf y c φ, ptOf_mem hc φ⟩) ⟨fun φ ψ h ↦ ?_,
    fun w ↦ ?_⟩).symm
  · obtain ⟨s, -, hs⟩ :=
      (Equivalence.eqvGen_iff (scale_equivalence (mCoordIdeal y))).mp (Quot.eqvGen_exact h)
    have hs1 : ∀ k, s k = 1 := fun k ↦ by
      have := congrFun hs ⟨k, c k⟩
      simp only [ptOf_chart hc, mul_one] at this
      exact this.symm
    have hpt : ptOf y c ψ = ptOf y c φ := by
      funext p
      have := congrFun hs p
      simp only [hs1, one_mul] at this
      exact this
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
    rintro _ ⟨p, rfl⟩
    exact congrFun hpt.symm p
  · obtain ⟨⟨z, hz⟩, rfl⟩ := Quot.exists_rep w
    obtain ⟨φ, hφ, hzc⟩ := exists_ptOf hP hc hz
    exact ⟨φ, (Quot.sound ⟨fun k ↦ (z ⟨k, c k⟩)⁻¹, fun k ↦ inv_ne_zero (hzc k), hφ⟩).symm⟩

end CoordCurveDegree

theorem CoordCurveDegree.full : CoordCurveDegree.Statement :=
  fun _ _ _ _ _ _ _ _ hP ↦ CoordCurveDegree.degC_eq hP

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
