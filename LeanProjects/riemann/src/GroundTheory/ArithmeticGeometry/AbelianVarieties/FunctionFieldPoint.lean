import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KernelCard

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

section Generic

noncomputable def genX : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W (C X))

noncomputable def genY : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W Y)

theorem genX_eq : genX W = algebraMap F[X] W.toAffine.FunctionField X := rfl

theorem transcendental_genX : Transcendental F (genX W) := by
  rw [transcendental_iff_injective]
  intro p q h
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply] at h
  exact (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    (FaithfulSMul.algebraMap_injective F[X] W.toAffine.CoordinateRing) h

theorem aeval_genX_eq_zero_iff (p : F[X]) : aeval (genX W) p = 0 ↔ p = 0 := by
  have := (transcendental_iff_injective.mp (transcendental_genX W))
  exact ⟨fun h => this (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem equation_gen : (W.baseChange W.toAffine.FunctionField).toAffine.Equation (genX W) (genY W) := by
  have h0 : CoordinateRing.mk W W.toAffine.polynomial = 0 := AdjoinRoot.mk_self
  have h1 := congrArg (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) h0
  rw [equation_iff]
  simp only [Affine.polynomial, map_sub, map_add, map_mul, map_pow, map_zero] at h1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, genX, genY]
  have e : ∀ a : F, algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W (C (C a))) = algebraMap F W.toAffine.FunctionField a := fun a => rfl
  simp only [C_add, C_mul, map_add, map_mul, e] at h1
  linear_combination h1

end Generic

section Lift

variable {L : Type*} [Field L] [Algebra F L] {u v : L}

private theorem eval₂_polynomial (h : (W.baseChange L).toAffine.Equation u v) :
    W.toAffine.polynomial.eval₂ (eval₂RingHom (algebraMap F L) u) v = 0 := by
  have e := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom, eval₂_X, eval₂_C]
  linear_combination e

noncomputable def evalAt (h : (W.baseChange L).toAffine.Equation u v) :
    W.toAffine.CoordinateRing →ₐ[F] L where
  __ := AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
  commutes' a := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply F F[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    simp

theorem evalAt_mk (h : (W.baseChange L).toAffine.Equation u v) (p : F[X][Y]) :
    evalAt W h (CoordinateRing.mk W p) = p.eval₂ (eval₂RingHom (algebraMap F L) u) v := by
  change AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
    (AdjoinRoot.mk _ p) = _
  rw [AdjoinRoot.lift_mk]

theorem evalAt_algebraMap (h : (W.baseChange L).toAffine.Equation u v) (p : F[X]) :
    evalAt W h (algebraMap F[X] W.toAffine.CoordinateRing p) = aeval u p := by
  rw [AdjoinRoot.algebraMap_eq]
  change AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
    (AdjoinRoot.of _ p) = _
  rw [AdjoinRoot.lift_of, coe_eval₂RingHom, aeval_def]

instance : Module.Finite F[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W.toAffine)

instance : Algebra.IsIntegral F[X] W.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _

theorem evalAt_injective (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    Function.Injective (evalAt W h) := by
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (evalAt W h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := F[X])
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [evalAt_algebraMap]
    exact ⟨fun hp => (transcendental_iff_injective.mp hu) (by rw [hp, map_zero]), fun hp => by
      rw [hp, map_zero]⟩
  intro a ha
  rw [← RingHom.mem_ker, hker] at ha
  exact ha

noncomputable def liftPoint (h : (W.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) : W.toAffine.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (evalAt_injective W h hu)

theorem liftPoint_algebraMap (h : (W.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) (a : W.toAffine.CoordinateRing) :
    liftPoint W h hu (algebraMap _ _ a) = evalAt W h a :=
  IsFractionRing.lift_algebraMap (evalAt_injective W h hu) a

theorem liftPoint_genX (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    liftPoint W h hu (genX W) = u := by
  rw [genX, liftPoint_algebraMap, evalAt_mk]
  simp

theorem liftPoint_genY (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    liftPoint W h hu (genY W) = v := by
  rw [genY, liftPoint_algebraMap, evalAt_mk]
  simp

end Lift

section GenericPoint

private noncomputable def coefB : W.toAffine.FunctionField :=
  algebraMap F _ W.a₁ * genX W + algebraMap F _ W.a₃

private noncomputable def coefC : W.toAffine.FunctionField :=
  genX W ^ 3 + algebraMap F _ W.a₂ * genX W ^ 2 + algebraMap F _ W.a₄ * genX W + algebraMap F _ W.a₆

private theorem genY_sq : genY W ^ 2 + coefB W * genY W - coefC W = 0 := by
  have e := (equation_iff _ _).mp (equation_gen W)
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [coefB, coefC]
  linear_combination e

theorem genY_ne_zero : genY W ≠ 0 := by
  rw [genY, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  intro h
  have := CoordinateRing.smul_basis_eq_zero (W' := W.toAffine) (p := 0) (q := 1)
    (by rw [zero_smul, zero_add, one_smul]; exact h)
  exact one_ne_zero this.2

theorem genY_not_mem : genY W ∉ IntermediateField.adjoin F {genX W} := by
  intro h
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff F (genY W)).mp h
  by_cases hs : aeval (genX W) s = 0
  · rw [hs, div_zero] at hrs; exact genY_ne_zero W hrs
  have key : genY W * aeval (genX W) s = aeval (genX W) r := by rw [hrs, div_mul_cancel₀ _ hs]
  simp only [genX_eq, aeval_algebraMap_apply, aeval_X_left, AlgHom.id_apply, genY] at key hs
  rw [IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField,
    IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField,
    ← map_mul, (IsFractionRing.injective _ _).eq_iff] at key
  have h0 : (-r) • (1 : W.toAffine.CoordinateRing) + s • CoordinateRing.mk W Y = 0 := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_neg]; linear_combination key
  exact hs (by rw [(CoordinateRing.smul_basis_eq_zero h0).2, map_zero])

theorem adjoin_genX_genY : IntermediateField.adjoin F {genX W, genY W} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  have mem : ∀ a : W.toAffine.CoordinateRing,
      algebraMap _ W.toAffine.FunctionField a ∈ IntermediateField.adjoin F {genX W, genY W} := by
    intro a
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
      refine mul_mem ?_ (pow_mem (IntermediateField.subset_adjoin F _ (by simp [genY])) _)
      induction c using Polynomial.induction_on' with
      | add p q hp hq => rw [C_add, map_add, map_add]; exact add_mem hp hq
      | monomial m d =>
        rw [← C_mul_X_pow_eq_monomial, C_mul, C_pow, map_mul, map_mul, map_pow, map_pow]
        refine mul_mem ?_ (pow_mem (IntermediateField.subset_adjoin F _ (by simp [genX])) _)
        exact IntermediateField.algebraMap_mem _ d
  exact div_mem (mem a) (mem b)

theorem finrank_adjoin_genX : Module.finrank (IntermediateField.adjoin F {genX W})
    W.toAffine.FunctionField = 2 := by
  set E1 := IntermediateField.adjoin F {genX W}
  have hx : genX W ∈ E1 := IntermediateField.mem_adjoin_simple_self F _
  have hb : coefB W ∈ E1 := by
    simp only [coefB]
    exact add_mem (mul_mem (IntermediateField.algebraMap_mem _ _) hx)
      (IntermediateField.algebraMap_mem _ _)
  have hc : coefC W ∈ E1 := by
    simp only [coefC]
    exact add_mem (add_mem (add_mem (pow_mem hx 3)
      (mul_mem (IntermediateField.algebraMap_mem _ _) (pow_mem hx 2)))
      (mul_mem (IntermediateField.algebraMap_mem _ _) hx)) (IntermediateField.algebraMap_mem _ _)
  set q : E1[X] := X ^ 2 + C ⟨coefB W, hb⟩ * X - C ⟨coefC W, hc⟩
  have hq : aeval (genY W) q = 0 := by
    simp only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    exact genY_sq W
  have hqdeg : q.natDegree = 2 := by simp only [q]; compute_degree!
  have hq0 : q ≠ 0 := fun h => by rw [h, natDegree_zero] at hqdeg; exact absurd hqdeg (by decide)
  have hint : IsIntegral E1 (genY W) := (show IsAlgebraic E1 (genY W) from ⟨q, hq0, hq⟩).isIntegral
  have hdeg : (minpoly E1 (genY W)).natDegree = 2 := by
    have hle : (minpoly E1 (genY W)).natDegree ≤ 2 := by
      rw [← hqdeg]
      exact natDegree_le_of_dvd (minpoly.dvd E1 _ hq) hq0
    have hne1 : (minpoly E1 (genY W)).natDegree ≠ 1 := by
      intro h1
      rw [minpoly.natDegree_eq_one_iff] at h1
      obtain ⟨z, hz⟩ := h1
      exact genY_not_mem W (hz ▸ z.2)
    have hpos := minpoly.natDegree_pos hint
    omega
  have htop : IntermediateField.adjoin E1 {genY W} = ⊤ := by
    rw [← IntermediateField.restrictScalars_eq_top_iff (K := F),
      IntermediateField.adjoin_simple_adjoin_simple]
    exact adjoin_genX_genY W
  rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hint, hdeg]

noncomputable instance : DecidableEq W.toAffine.FunctionField := Classical.decEq _

variable [W.IsElliptic]

instance (A : Type*) [Field A] [Algebra F A] : (W.baseChange A).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance

noncomputable def genericPoint : (W.baseChange W.toAffine.FunctionField).toAffine.Point :=
  .some (genX W) (genY W) (equation_iff_nonsingular.mp (equation_gen W))

theorem map_liftPoint_genericPoint {L : Type*} [Field L] [Algebra F L] [DecidableEq L] {u v : L}
    (h : (W.baseChange L).toAffine.Nonsingular u v) (hu : Transcendental F u) :
    Point.map (liftPoint W h.1 hu) (genericPoint W) = .some u v h := by
  simp only [genericPoint, Point.map]
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Point.some.injEq]
  exact ⟨liftPoint_genX W h.1 hu, liftPoint_genY W h.1 hu⟩

end GenericPoint

end GroundTheory.Arith.Abelian
