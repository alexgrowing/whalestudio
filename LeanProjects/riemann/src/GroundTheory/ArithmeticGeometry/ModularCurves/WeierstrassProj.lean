import Mathlib
import GroundTheory.ArithmeticGeometry.ModularCurves.WeierstrassCharts

open CategoryTheory AlgebraicGeometry DirectSum

universe u

namespace GroundTheory.Arith.Modular

section QuotientGrading

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A)
  [GradedAlgebra 𝒜] (I : Ideal A)

def quotGrading (n : ℕ) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

omit [GradedAlgebra 𝒜] in
lemma mk_mem_quotGrading {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    Ideal.Quotient.mk I a ∈ quotGrading 𝒜 I n :=
  ⟨a, ha, rfl⟩

instance quotGrading_gradedMonoid : SetLike.GradedMonoid (quotGrading 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  mul_mem := by
    rintro i j _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, SetLike.GradedMul.mul_mem ha hb, by simp⟩

def quotComponent (n : ℕ) : 𝒜 n →+ quotGrading 𝒜 I n where
  toFun x := ⟨Ideal.Quotient.mk I x, mk_mem_quotGrading 𝒜 I x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def quotDecomposeHom : A →+ ⨁ n, quotGrading 𝒜 I n :=
  (DirectSum.map (quotComponent 𝒜 I)).comp (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable {𝒜 I}

lemma quotDecomposeHom_of_mem (hI : I.IsHomogeneous 𝒜) {a : A} (ha : a ∈ I) :
    quotDecomposeHom 𝒜 I a = 0 := by
  ext n
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 a n : A) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI n ha

variable (hI : I.IsHomogeneous 𝒜)
include hI

def quotDecompose : A ⧸ I →+ ⨁ n, quotGrading 𝒜 I n :=
  QuotientAddGroup.lift I.toAddSubgroup (quotDecomposeHom 𝒜 I)
    (fun _ ha => quotDecomposeHom_of_mem hI ha)

omit hI in
lemma quotDecomposeHom_apply (a : A) : quotDecomposeHom 𝒜 I a =
    DirectSum.map (quotComponent 𝒜 I) (DirectSum.decompose 𝒜 a) := rfl

omit hI [GradedAlgebra 𝒜] in
lemma coe_comp_map_quotComponent :
    (DirectSum.coeAddMonoidHom (quotGrading 𝒜 I)).comp (DirectSum.map (quotComponent 𝒜 I)) =
      (Ideal.Quotient.mk I).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
  ext n x
  simp [DirectSum.map_of, quotComponent]

omit hI in
lemma coe_quotDecomposeHom (a : A) :
    DirectSum.coeAddMonoidHom (quotGrading 𝒜 I) (quotDecomposeHom 𝒜 I a) =
      Ideal.Quotient.mk I a := by
  rw [quotDecomposeHom_apply]
  have := congrArg (fun φ => φ (DirectSum.decompose 𝒜 a)) (coe_comp_map_quotComponent (𝒜 := 𝒜) (I := I))
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
  rw [this]
  exact congrArg (Ideal.Quotient.mk I) ((DirectSum.decompose 𝒜).symm_apply_apply a)

omit hI in
lemma quotDecomposeHom_of_mem_grading {n : ℕ} {a : A} (ha : a ∈ 𝒜 n) :
    quotDecomposeHom 𝒜 I a = DirectSum.of (fun n => quotGrading 𝒜 I n) n
      ⟨Ideal.Quotient.mk I a, mk_mem_quotGrading 𝒜 I ha⟩ := by
  rw [quotDecomposeHom_apply, DirectSum.decompose_of_mem 𝒜 ha, DirectSum.map_of]
  rfl

@[instance_reducible]
def quotGradedAlgebra : GradedAlgebra (quotGrading 𝒜 I) where
  decompose' := quotDecompose hI
  left_inv q := by
    induction q using Quotient.inductionOn' with
    | h a => exact coe_quotDecomposeHom a
  right_inv d := by
    induction d using DirectSum.induction_on with
    | zero => simp
    | of n q =>
      obtain ⟨q, a, ha, rfl⟩ := q
      rw [DirectSum.coeAddMonoidHom_of]
      exact quotDecomposeHom_of_mem_grading ha
    | add d e hd he => rw [map_add, map_add, hd, he]

end QuotientGrading

section Scale

variable {R : Type u} [CommRing R] {σ : Type*} {Q : Type*} [CommRing Q] (π : MvPolynomial σ R →+* Q)
  (i : σ)

noncomputable def scale : MvPolynomial σ R →+* Localization.Away (π (MvPolynomial.X i)) :=
  MvPolynomial.eval₂Hom ((algebraMap Q _).comp (π.comp MvPolynomial.C))
    (fun j => algebraMap Q _ (π (MvPolynomial.X j)) *
      IsLocalization.Away.invSelf (S := Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i)))

theorem scale_monomial (e : σ →₀ ℕ) (c : R) :
    scale π i (MvPolynomial.monomial e c) *
        algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ e.degree) =
      algebraMap Q _ (π (MvPolynomial.monomial e c)) := by
  set u := IsLocalization.Away.invSelf (S := Localization.Away (π (MvPolynomial.X i)))
    (π (MvPolynomial.X i))
  have hu : algebraMap Q _ (π (MvPolynomial.X i)) * u = 1 := IsLocalization.Away.mul_invSelf _
  have hdeg : e.degree = ∑ j ∈ e.support, e j := rfl
  have hinv : (e.prod fun _ k => u ^ k) *
      algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ e.degree) = 1 := by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, map_pow, ← hdeg, ← mul_pow, mul_comm, hu, one_pow]
  simp only [scale, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial, RingHom.comp_apply]
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul, mul_assoc, mul_assoc, hinv, mul_one, MvPolynomial.monomial_eq, map_mul,
    map_mul, map_finsuppProd, map_finsuppProd]
  simp only [map_pow]

theorem scale_homog {m : ℕ} {a : MvPolynomial σ R} (ha : a.IsHomogeneous m) :
    scale π i a * algebraMap Q (Localization.Away (π (MvPolynomial.X i))) (π (MvPolynomial.X i) ^ m) =
      algebraMap Q _ (π a) := by
  conv_lhs => rw [a.as_sum]
  conv_rhs => rw [a.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hdeg : e.degree = m := by
    have := ha (MvPolynomial.mem_support_iff.mp he)
    rwa [Finsupp.degree_eq_weight_one]
  rw [← hdeg]
  exact scale_monomial π i e _

end Scale

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Weierstrass

open MvPolynomial

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

abbrev grading (R : Type u) [CommRing R] : ℕ → Submodule R (MvPolynomial (Fin 3) R) :=
  homogeneousSubmodule (Fin 3) R

noncomputable def cubicIdeal : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {W.toProjective.polynomial}

theorem isHomogeneous_cubic : W.toProjective.polynomial.IsHomogeneous 3 := by
  have hX := isHomogeneous_X R (0 : Fin 3)
  have hY := isHomogeneous_X R (1 : Fin 3)
  have hZ := isHomogeneous_X R (2 : Fin 3)
  have hC := fun a : R => isHomogeneous_C (Fin 3) a
  simp only [WeierstrassCurve.Projective.polynomial]
  exact IsHomogeneous.sub (IsHomogeneous.add (IsHomogeneous.add ((hY.pow 2).mul hZ)
    ((((hC _).mul hX).mul hY).mul hZ)) (((hC _).mul hY).mul (hZ.pow 2)))
    (IsHomogeneous.add (IsHomogeneous.add (IsHomogeneous.add (hX.pow 3)
      (((hC _).mul (hX.pow 2)).mul hZ)) (((hC _).mul hX).mul (hZ.pow 2))) ((hC _).mul (hZ.pow 3)))

theorem cubicIdeal_isHomogeneous : (cubicIdeal W).IsHomogeneous (grading R) :=
  Ideal.homogeneous_span _ _ (by
    rintro _ rfl
    exact ⟨3, (mem_homogeneousSubmodule 3 _).2 (isHomogeneous_cubic W)⟩)

noncomputable abbrev HomRing : Type u := MvPolynomial (Fin 3) R ⧸ cubicIdeal W

noncomputable abbrev homGrading : ℕ → Submodule R (HomRing W) := quotGrading (grading R) (cubicIdeal W)

noncomputable instance : GradedAlgebra (homGrading W) :=
  quotGradedAlgebra (cubicIdeal_isHomogeneous W)

noncomputable abbrev Curve : Scheme.{u} := Proj (homGrading W)

noncomputable abbrev var (j : Fin 3) : HomRing W := Ideal.Quotient.mk (cubicIdeal W) (X j)

theorem var_mem (j : Fin 3) : var W j ∈ homGrading W 1 :=
  mk_mem_quotGrading _ _ (isHomogeneous_X R j)

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

noncomputable abbrev π : MvPolynomial (Fin 3) R →+* HomRing W := Ideal.Quotient.mk (cubicIdeal W)

theorem π_cubic : π W W.toProjective.polynomial = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)

noncomputable def scalarAway (j : Fin 3) : R →+* Away (homGrading W) (var W j) :=
  (fromZeroRingHom (homGrading W) _).comp (algebraMap R (homGrading W 0))

noncomputable def frac (j k : Fin 3) : Away (homGrading W) (var W j) :=
  Away.mk (homGrading W) (var_mem W j) 1 (var W k) (by simpa using var_mem W k)

noncomputable abbrev vinv (j : Fin 3) : Localization.Away (var W j) :=
  IsLocalization.Away.invSelf (S := Localization.Away (var W j)) (var W j)

theorem val_frac (j k : Fin 3) :
    (frac W j k).val = algebraMap (HomRing W) (Localization.Away (var W j)) (var W k) * vinv W j := by
  rw [frac, Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one, vinv,
    IsLocalization.Away.invSelf]
  congr 2
  exact Subtype.ext (pow_one _)

theorem val_scalarAway (j : Fin 3) (r : R) :
    (scalarAway W j r).val = algebraMap (HomRing W) (Localization.Away (var W j)) (algebraMap R _ r) := by
  simp [scalarAway, fromZeroRingHom]
  rfl

theorem scale_eq_zero_of_mem {j : Fin 3} : scale (π W) j W.toProjective.polynomial = 0 := by
  have h := scale_homog (π W) j (isHomogeneous_cubic W)
  rw [π_cubic, map_zero] at h
  have hu : algebraMap (HomRing W) (Localization.Away (var W j)) (var W j) * vinv W j = 1 :=
    IsLocalization.Away.mul_invSelf _
  have : scale (π W) j W.toProjective.polynomial =
      scale (π W) j W.toProjective.polynomial *
        algebraMap (HomRing W) (Localization.Away (var W j)) (var W j ^ 3) * vinv W j ^ 3 := by
    rw [map_pow, mul_assoc, ← mul_pow, hu, one_pow, mul_one]
  rw [this, h, zero_mul]

end Weierstrass

namespace Weierstrass

open MvPolynomial HomogeneousLocalization

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

theorem constantCoeff_cubic : constantCoeff W.toProjective.polynomial = 0 := by
  simp [WeierstrassCurve.Projective.polynomial]

theorem algebraMap_zero_bijective : Function.Bijective (algebraMap R (homGrading W 0)) := by
  constructor
  · intro r s h
    have h' : π W (C (r - s)) = 0 := by
      have := congrArg Subtype.val h
      simp only [SetLike.GradeZero.coe_algebraMap] at this
      rw [map_sub, map_sub, sub_eq_zero]
      exact this
    rw [Ideal.Quotient.eq_zero_iff_mem, cubicIdeal, Ideal.mem_span_singleton'] at h'
    obtain ⟨g, hg⟩ := h'
    have := congrArg constantCoeff hg
    rw [map_mul, constantCoeff_cubic, mul_zero, constantCoeff_C] at this
    exact sub_eq_zero.1 this.symm
  · rintro ⟨q, P, hP, rfl⟩
    have hP' : P.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 P).1 hP
    have h0 : P.totalDegree = 0 := by
      by_cases hP0 : P = 0
      · simp [hP0]
      · exact hP'.totalDegree hP0
    obtain ⟨r, rfl⟩ : ∃ r, P = C r := ⟨_, totalDegree_eq_zero_iff_eq_C.1 h0⟩
    exact ⟨r, Subtype.ext rfl⟩

noncomputable def zeroEquiv : R ≃+* homGrading W 0 :=
  RingEquiv.ofBijective (algebraMap R (homGrading W 0)) (algebraMap_zero_bijective W)

noncomputable def toSpec : Curve W ⟶ Spec (.of R) :=
  Proj.toSpecZero (homGrading W) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (homGrading W 0)))

instance : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R (homGrading W 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R (homGrading W 0))) :=
    (zeroEquiv W).toCommRingCatIso.isIso_hom
  infer_instance

instance : IsScalarTower R (homGrading W 0) (HomRing W) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := homGrading W 0) (A := HomRing W) (fun _ => rfl)

instance : Algebra.FiniteType (homGrading W 0) (HomRing W) := by
  have : Algebra.FiniteType R (HomRing W) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType R _ _

instance : IsProper (toSpec W) := by
  unfold toSpec
  infer_instance

noncomputable def chartZι : Spec (.of (Away (homGrading W) (var W 2))) ⟶ Curve W :=
  Proj.awayι (homGrading W) (var W 2) (var_mem W 2) one_pos

noncomputable def chartYι : Spec (.of (Away (homGrading W) (var W 1))) ⟶ Curve W :=
  Proj.awayι (homGrading W) (var W 1) (var_mem W 1) one_pos

end Weierstrass

end GroundTheory.Arith.Modular
