import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIntegralModelOfForms

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors

section Valuation

variable (V : Type*) [CommRing V] [IsDomain V] [ValuationRing V] {K : Type*} [Field K] [CharZero K]
  [Algebra V K] [IsFractionRing V K] {L : Type*} [Field L] [Algebra K L] [IsAlgClosed L]
  {W : WeierstrassCurve K} [W.IsElliptic]

end Valuation

section Good

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

end Good

instance isDiscreteValuationRing_valuationSubringAtPrime {R : Type*} [CommRing R]
    [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : HeightOneSpectrum R) : IsDiscreteValuationRing (p.valuationSubringAtPrime K) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R p.ne_bot _

section Global

variable {M : Type*} [Field M] [CharZero M] {L : Type*} [Field L] [Algebra M L] [IsAlgClosed L]
  {W : WeierstrassCurve M} [W.IsElliptic]

theorem exists_model_ringOfIntegers (hj : IsIntegral ℤ W.j) (h : HasRationalTorsion W L 12)
    (M' : Type*) [Field M'] [Algebra M M'] :
    ∃ (C : VariableChange M') (W₀ : WeierstrassCurve (𝓞 M')),
      C • W.baseChange M' = W₀.baseChange M' ∧ W₀.Δ = 1 := by
  have : IsIntegrallyClosedIn (𝓞 M) M := inferInstance
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model (𝓞 M) ⟨⟨W.j, hj⟩, rfl⟩ h
  refine ⟨C.map (algebraMap M M'), W₀.map (algebraMap (𝓞 M) (𝓞 M')), ?_, by rw [map_Δ, h₀, map_one]⟩
  rw [WeierstrassCurve.baseChange, map_variableChange, e]
  rfl

end Global

section Finite

theorem finite_nsmul_eq_zero_mul {G : Type*} [AddCommGroup G] {m n : ℕ}
    (hm : {x : G | m • x = 0}.Finite) (hn : {x : G | n • x = 0}.Finite) :
    {x : G | (m * n) • x = 0}.Finite := by
  refine Set.Finite.of_finite_fibers (fun x => m • x) (hn.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    simpa [mul_nsmul] using hx
  · rintro _ ⟨x, -, rfl⟩
    refine (hm.image (· + x)).subset fun y hy => ⟨y - x, ?_, sub_add_cancel _ _⟩
    have : m • y = m • x := hy.2
    simp [smul_sub, this]

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem finite_points_of_root {p : F[X]} (hp : p ≠ 0) {s : Set W.toAffine.Point}
    (hs : ∀ x y h, Point.some x y h ∈ s → p.eval x = 0) : s.Finite := by
  refine Set.Finite.of_finite_fibers Point.xRep
    ((((p.rootSet_finite F).image fun x => ![x, 1]).insert ![1, 0]).subset ?_) ?_
  · rintro _ ⟨_ | ⟨x, y, h⟩, hP, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, by simpa [mem_rootSet, hp] using hs x y h hP, rfl⟩
  · rintro _ ⟨P, -, rfl⟩
    exact (Set.toFinite {P, -P}).subset fun Q hQ => Point.eq_or_eq_neg_of_xRep_eq_xRep hQ.2

variable [CharZero F] [DecidableEq F]

theorem finite_two_torsion : {P : W.toAffine.Point | 2 • P = 0}.Finite := by
  refine finite_points_of_root (W.Ψ₂Sq_ne_zero (by norm_num)) fun x y h hP => ?_
  have hy : y = W.toAffine.negY x y := by
    by_contra hy
    rw [Set.mem_setOf_eq, two_nsmul, Point.add_self_of_Y_ne hy] at hP
    exact Point.some_ne_zero _ hP
  have hE := (equation_iff ..).mp h.1
  rw [negY] at hy
  simp only [Ψ₂Sq, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination -4 * hE + (2 * y + W.a₁ * x + W.a₃) * hy

theorem finite_three_torsion : {P : W.toAffine.Point | 3 • P = 0}.Finite :=
  finite_points_of_root (W.Ψ₃_ne_zero three_ne_zero) fun _ _ h hP =>
    (three_nsmul_eq_zero_iff h).mp hP

theorem finite_twelve_torsion : {P : W.toAffine.Point | 12 • P = 0}.Finite :=
  finite_nsmul_eq_zero_mul (m := 2 * 2) (n := 3)
    (finite_nsmul_eq_zero_mul finite_two_torsion finite_two_torsion) finite_three_torsion

end Finite

theorem exists_finite_hasRationalTorsion_twelve {K : Type*} [Field K] [CharZero K]
    (W : WeierstrassCurve K) (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ∃ M : IntermediateField K L, FiniteDimensional K M ∧
      HasRationalTorsion (W.baseChange M) L 12 := by
  classical
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let c : (W.baseChange L).toAffine.Point → Set L
    | .zero => ∅
    | .some x y _ => {x, y}
  have hfin : (⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P).Finite := by
    refine finite_twelve_torsion.biUnion ?_
    rintro (_ | _) - <;> simp [c]
  have := hfin.to_subtype
  refine ⟨IntermediateField.adjoin K _, IntermediateField.finiteDimensional_adjoin
    (S := ⋃ P ∈ {P : (W.baseChange L).toAffine.Point | 12 • P = 0}, c P)
    fun x _ => Algebra.IsIntegral.isIntegral x, ?_⟩
  rw [hasRationalTorsion_iff]
  intro x y h h0
  exact ⟨⟨⟨x, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩,
    ⟨⟨y, IntermediateField.subset_adjoin _ _ (Set.mem_biUnion (x := .some x y h) h0
      (by simp [c]))⟩, rfl⟩⟩

theorem exists_finite_model_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : IsIntegral ℤ W.j) :
    ∃ M : IntermediateField K (AlgebraicClosure K), NumberField M ∧
      HasRationalTorsion (W.baseChange M) (AlgebraicClosure K) 12 ∧
      ∃ (C : VariableChange M) (W₀ : WeierstrassCurve (𝓞 M)),
        C • W.baseChange M = W₀.baseChange M ∧ W₀.Δ = 1 := by
  obtain ⟨M, hM, h⟩ := exists_finite_hasRationalTorsion_twelve W (AlgebraicClosure K)
  have : NumberField M := NumberField.of_module_finite K M
  have : (W.baseChange M).IsElliptic := inferInstanceAs (W.map (algebraMap K M)).IsElliptic
  have hj' : IsIntegral ℤ (W.baseChange M).j := by
    rw [show (W.baseChange M).j = algebraMap K M W.j from W.map_j _]
    exact hj.algebraMap
  exact ⟨M, inferInstance, h, exists_model_ringOfIntegers hj' h M⟩

end GlobalTheory
