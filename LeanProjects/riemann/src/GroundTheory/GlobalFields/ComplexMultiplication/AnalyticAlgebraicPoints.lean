import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicGerm
import GroundTheory.GlobalFields.ComplexMultiplication.UniformizationGroup
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogeny

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem mem_meroSubalgebra {f : ℂ → ℂ} : f ∈ meroSubalgebra ↔ Meromorphic f := Iff.rfl

def mero (f : ℂ → ℂ) (hf : Meromorphic f) : meroSubalgebra := ⟨f, mem_meroSubalgebra.2 hf⟩

@[simp] theorem coe_mero (f : ℂ → ℂ) (hf : Meromorphic f) : (mero f hf : ℂ → ℂ) = f := rfl

theorem mkₐ_eq_germ {f : ℂ → ℂ} (hf : Meromorphic f) :
    Ideal.Quotient.mkₐ ℂ meroNull (mero f hf) = germ f :=
  (germ_of hf).symm

theorem mkₐ_eq_zero_iff (a : meroSubalgebra) :
    Ideal.Quotient.mkₐ ℂ meroNull a = 0 ↔ (a : ℂ → ℂ) =ᶠ[codiscrete ℂ] 0 := by
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem mkₐ_eq_mkₐ_iff (a b : meroSubalgebra) :
    Ideal.Quotient.mkₐ ℂ meroNull a = Ideal.Quotient.mkₐ ℂ meroNull b ↔
      (a : ℂ → ℂ) =ᶠ[codiscrete ℂ] b := by
  rw [← sub_eq_zero, ← map_sub, mkₐ_eq_zero_iff]
  exact (Filter.eventuallyEq_iff_sub (f := (a : ℂ → ℂ)) (g := b)).symm

theorem preimage_affine_mem_codiscrete {S : Set ℂ} (hS : S ∈ codiscrete ℂ) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : (fun z ↦ t * z + s) ⁻¹' S ∈ codiscrete ℂ := by
  have h := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hS
  rw [codiscrete, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x _
  have hc : Continuous fun z : ℂ ↦ t * z + s := by fun_prop
  have hmaps : MapsTo (fun z : ℂ ↦ t * z + s) {x}ᶜ {t * x + s}ᶜ := fun z hz hz' ↦ hz (by
    simp only [mem_singleton_iff, add_left_inj] at hz' ⊢
    exact mul_left_cancel₀ ht hz')
  have := (hc.continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps) (h _ (mem_univ _))
  rw [compl_univ, union_empty] at this ⊢
  exact this

theorem eventually_affine {p : ℂ → Prop} (h : ∀ᶠ z in codiscrete ℂ, p z) {t : ℂ} (ht : t ≠ 0)
    (s : ℂ) : ∀ᶠ z in codiscrete ℂ, p (t * z + s) :=
  preimage_affine_mem_codiscrete h ht s

theorem eventually_notMem_lattice (L : PeriodPair) : ∀ᶠ z in codiscrete ℂ, z ∉ L.lattice := by
  filter_upwards [eventually_analyticAt L.meromorphic_weierstrassP] with z hz hzL
  have h := hz.meromorphicOrderAt_nonneg
  rw [L.order_weierstrassP z hzL] at h
  exact absurd h (by decide)

theorem meromorphic_eval_comp {f : ℂ → ℂ} (hf : Meromorphic f) (p : ℂ[X]) :
    Meromorphic fun z ↦ p.eval (f z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact fun x ↦ (hp x).add (hq x)
  | monomial n a =>
    simp only [eval_monomial]
    exact fun x ↦ (MeromorphicAt.const a x).mul ((hf x).pow n)

theorem germ_aeval {f : ℂ → ℂ} (hf : Meromorphic f) (p : ℂ[X]) :
    aeval (germ f) p = germ fun z ↦ p.eval (f z) := by
  have hp := meromorphic_eval_comp hf p
  rw [← mkₐ_eq_germ hf, ← mkₐ_eq_germ hp, Polynomial.aeval_algHom_apply]
  congr 1
  apply Subtype.ext
  rw [← Subalgebra.aeval_coe]
  funext z
  rw [Polynomial.aeval_fn_apply]
  simp [Polynomial.aeval_def, Polynomial.eval₂_id]

theorem ne_algebraMap_of_transcendental {u : MeroField} (hu : Transcendental ℂ u) (c : ℂ) :
    u ≠ algebraMap ℂ MeroField c := by
  rintro rfl
  exact hu (isAlgebraic_algebraMap c)

section Points

variable {W : WeierstrassCurve ℂ}

theorem equation_germ {x y : ℂ → ℂ} (hx : Meromorphic x) (hy : Meromorphic y)
    (h : ∀ᶠ z in codiscrete ℂ, W.toAffine.Equation (x z) (y z)) :
    (W.baseChange MeroField).toAffine.Equation (germ x) (germ y) := by
  set X : meroSubalgebra := mero x hx
  set Y : meroSubalgebra := mero y hy
  have key : Ideal.Quotient.mkₐ ℂ meroNull (Y ^ 2 + algebraMap ℂ _ W.a₁ * X * Y +
      algebraMap ℂ _ W.a₃ * Y - (X ^ 3 + algebraMap ℂ _ W.a₂ * X ^ 2 + algebraMap ℂ _ W.a₄ * X +
      algebraMap ℂ _ W.a₆)) = 0 := by
    rw [mkₐ_eq_zero_iff]
    filter_upwards [h] with z hz
    rw [equation_iff] at hz
    simp only [Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow,
      Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply,
      Pi.zero_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, X, Y, coe_mero]
    linear_combination hz
  rw [← mkₐ_eq_germ hx, ← mkₐ_eq_germ hy, equation_iff]
  simp only [map_sub, map_add, map_mul, map_pow, AlgHom.commutes] at key
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  linear_combination key

theorem coords_of_add_some {x₁ y₁ x₂ y₂ x₃ y₃ : ℂ} {k₁ : W.toAffine.Nonsingular x₁ y₁}
    {k₂ : W.toAffine.Nonsingular x₂ y₂} {k₃ : W.toAffine.Nonsingular x₃ y₃} (hx : x₁ ≠ x₂)
    (h : Point.some x₁ y₁ k₁ + Point.some x₂ y₂ k₂ = Point.some x₃ y₃ k₃) :
    x₃ = W.toAffine.addX x₁ x₂ ((y₁ - y₂) / (x₁ - x₂)) ∧
      y₃ = W.toAffine.addY x₁ x₂ y₁ ((y₁ - y₂) / (x₁ - x₂)) := by
  rw [Point.add_some (fun h ↦ hx h.1), Point.some.injEq, slope_of_X_ne hx] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem add_some_germ {x₁ y₁ x₂ y₂ x₃ y₃ : ℂ → ℂ} (m₁ : Meromorphic x₁) (n₁ : Meromorphic y₁)
    (m₂ : Meromorphic x₂) (n₂ : Meromorphic y₂) (m₃ : Meromorphic x₃) (n₃ : Meromorphic y₃)
    {h₁ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₁) (germ y₁)}
    {h₂ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₂) (germ y₂)}
    {h₃ : (W.baseChange MeroField).toAffine.Nonsingular (germ x₃) (germ y₃)}
    (hx : germ x₁ ≠ germ x₂)
    (hpt : ∀ᶠ z in codiscrete ℂ, ∃ (k₁ : W.toAffine.Nonsingular (x₁ z) (y₁ z))
      (k₂ : W.toAffine.Nonsingular (x₂ z) (y₂ z)) (k₃ : W.toAffine.Nonsingular (x₃ z) (y₃ z)),
      Point.some _ _ k₁ + Point.some _ _ k₂ = Point.some _ _ k₃) :
    Point.some _ _ h₁ + Point.some _ _ h₂ = Point.some _ _ h₃ := by
  have hne : ∀ᶠ z in codiscrete ℂ, x₁ z - x₂ z ≠ 0 := by
    refine eventually_ne_zero_codiscrete (m₁.sub m₂) fun h ↦ hx ?_
    rw [germ_eq_germ_iff m₁ m₂, Filter.eventuallyEq_iff_sub]
    exact h
  set ℓ : ℂ → ℂ := fun z ↦ (y₁ z - y₂ z) / (x₁ z - x₂ z)
  have mℓ : Meromorphic ℓ := (n₁.sub n₂).div (m₁.sub m₂)
  have hℓ : germ ℓ = (germ y₁ - germ y₂) / (germ x₁ - germ x₂) := by
    rw [← germ_sub n₁ n₂, ← germ_sub m₁ m₂, ← germ_div (n₁.sub n₂) (m₁.sub m₂)]
    rfl
  have hxy : ¬(germ x₁ = germ x₂ ∧ germ y₁ = (W.baseChange MeroField).toAffine.negY (germ x₂) (germ y₂)) :=
    fun h ↦ hx h.1
  rw [Point.add_some hxy, Point.some.injEq, slope_of_X_ne hx, ← hℓ, ← mkₐ_eq_germ m₁,
    ← mkₐ_eq_germ m₂, ← mkₐ_eq_germ n₁, ← mkₐ_eq_germ mℓ, ← mkₐ_eq_germ m₃, ← mkₐ_eq_germ n₃]
  have e := baseChange_addX (W' := W) (Ideal.Quotient.mkₐ ℂ meroNull) (x₁ := mero x₁ m₁)
    (x₂ := mero x₂ m₂) (ℓ := mero ℓ mℓ)
  have e' := baseChange_addY (W' := W) (Ideal.Quotient.mkₐ ℂ meroNull) (x₁ := mero x₁ m₁)
    (x₂ := mero x₂ m₂) (y₁ := mero y₁ n₁) (ℓ := mero ℓ mℓ)
  rw [e, e', mkₐ_eq_mkₐ_iff, mkₐ_eq_mkₐ_iff]
  constructor
  · filter_upwards [hpt, hne] with z ⟨k₁, k₂, k₃, hz⟩ hz'
    obtain ⟨h1, -⟩ := coords_of_add_some (sub_ne_zero.1 hz') hz
    rw [coe_mero, h1]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ℓ, coe_mero]
  · filter_upwards [hpt, hne] with z ⟨k₁, k₂, k₃, hz⟩ hz'
    obtain ⟨-, h2⟩ := coords_of_add_some (sub_ne_zero.1 hz') hz
    rw [coe_mero, h2]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg,
      Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Pi.sub_apply, Pi.add_apply, Pi.mul_apply,
      Pi.neg_apply, Pi.pow_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ℓ, coe_mero]

end Points

section Lattice

variable (L : PeriodPair)

theorem meromorphic_weierstrassP_affine (t s : ℂ) : Meromorphic fun z ↦ ℘[L] (t * z + s) :=
  meromorphic_comp_affine L.meromorphic_weierstrassP t s

theorem meromorphic_derivWeierstrassP_half : Meromorphic fun z ↦ ℘'[L] z / 2 :=
  fun x ↦ (L.meromorphic_derivWeierstrassP x).div (MeromorphicAt.const 2 x)

theorem meromorphic_derivWeierstrassP_half_affine (t s : ℂ) :
    Meromorphic fun z ↦ ℘'[L] (t * z + s) / 2 :=
  meromorphic_comp_affine (meromorphic_derivWeierstrassP_half L) t s

theorem equation_affine (t s : ℂ) (ht : t ≠ 0) :
    ((weierstrassCurve L).baseChange MeroField).toAffine.Equation
      (germ fun z ↦ ℘[L] (t * z + s)) (germ fun z ↦ ℘'[L] (t * z + s) / 2) :=
  equation_germ (meromorphic_weierstrassP_affine L t s)
    (meromorphic_derivWeierstrassP_half_affine L t s) (by
      filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s] with z hz
      exact equation_weierstrassP L hz)

theorem equation_base :
    ((weierstrassCurve L).baseChange MeroField).toAffine.Equation
      (germ ℘[L]) (germ fun z ↦ ℘'[L] z / 2) := by
  have h := equation_affine L 1 0 one_ne_zero
  simp only [one_mul, add_zero] at h
  exact h

def basePoint : ((weierstrassCurve L).baseChange MeroField).toAffine.Point :=
  .some _ _ (equation_iff_nonsingular.1 (equation_base L))

def affinePoint (t s : ℂ) (ht : t ≠ 0) : ((weierstrassCurve L).baseChange MeroField).toAffine.Point :=
  .some _ _ (equation_iff_nonsingular.1 (equation_affine L t s ht))

theorem map_affineComp_basePoint (t s : ℂ) (ht : t ≠ 0) :
    Point.map (affineComp t s ht) (basePoint L) = affinePoint L t s ht := by
  simp only [basePoint, affinePoint, Point.map_some, Point.some.injEq]
  exact ⟨affineComp_germ t s ht L.meromorphic_weierstrassP,
    affineComp_germ t s ht (meromorphic_derivWeierstrassP_half L)⟩

theorem map_affineComp_affinePoint (t s t' s' : ℂ) (ht : t ≠ 0) (ht' : t' ≠ 0) :
    Point.map (affineComp t' s' ht') (affinePoint L t s ht) =
      affinePoint L (t * t') (t * s' + s) (mul_ne_zero ht ht') := by
  simp only [affinePoint, Point.map_some, Point.some.injEq]
  rw [affineComp_germ t' s' ht' (meromorphic_weierstrassP_affine L t s),
    affineComp_germ t' s' ht' (meromorphic_derivWeierstrassP_half_affine L t s)]
  have e : ∀ z : ℂ, t * (t' * z + s') + s = t * t' * z + (t * s' + s) := fun z ↦ by ring
  simp only [e, and_self]

theorem transcendental_germ_weierstrassP : Transcendental ℂ (germ ℘[L]) := by
  rintro ⟨p, hp0, hp⟩
  rw [germ_aeval L.meromorphic_weierstrassP,
    germ_eq_zero_iff (meromorphic_eval_comp L.meromorphic_weierstrassP p)] at hp
  obtain ⟨z, h1, h2⟩ := nonempty_of_mem_codiscrete
    (hp.and (eventually_codiscrete_eval_weierstrassP_ne_zero (L := L) hp0))
  exact h2 (by simpa using h1)

theorem transcendental_germ_weierstrassP_affine (t s : ℂ) (ht : t ≠ 0) :
    Transcendental ℂ (germ fun z ↦ ℘[L] (t * z + s)) := by
  rw [← affineComp_germ t s ht L.meromorphic_weierstrassP]
  intro h
  exact transcendental_germ_weierstrassP L
    ((isAlgebraic_algHom_iff (affineComp t s ht) (affineComp t s ht).toRingHom.injective).1 h)

theorem affinePoint_add {t₁ s₁ t₂ s₂ : ℂ} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h₃ : t₁ + t₂ ≠ 0)
    (hx : (germ fun z ↦ ℘[L] (t₁ * z + s₁)) ≠ germ fun z ↦ ℘[L] (t₂ * z + s₂)) :
    affinePoint L t₁ s₁ h₁ + affinePoint L t₂ s₂ h₂ = affinePoint L (t₁ + t₂) (s₁ + s₂) h₃ := by
  apply add_some_germ (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) (meromorphic_weierstrassP_affine L _ _)
    (meromorphic_derivWeierstrassP_half_affine L _ _) hx
  filter_upwards [eventually_affine (eventually_notMem_lattice L) h₁ s₁,
    eventually_affine (eventually_notMem_lattice L) h₂ s₂,
    eventually_affine (eventually_notMem_lattice L) h₃ (s₁ + s₂)] with z hz1 hz2 hz3
  have e : t₁ * z + s₁ + (t₂ * z + s₂) = (t₁ + t₂) * z + (s₁ + s₂) := by ring
  refine ⟨equation_iff_nonsingular.1 (equation_weierstrassP L hz1),
    equation_iff_nonsingular.1 (equation_weierstrassP L hz2),
    equation_iff_nonsingular.1 (equation_weierstrassP L hz3), ?_⟩
  have h := toPoint_add (L := L) (t₁ * z + s₁) (t₂ * z + s₂)
  rw [toPoint_of_notMem hz1, toPoint_of_notMem hz2, e, toPoint_of_notMem hz3] at h
  exact h.symm

theorem affinePoint_add_constMap (t s c : ℂ) (ht : t ≠ 0) :
    affinePoint L t s ht + constMap (weierstrassCurve L) MeroField (toPoint L c) =
      affinePoint L t (s + c) ht := by
  by_cases hc : c ∈ L.lattice
  · rw [toPoint_of_mem hc, map_zero, add_zero]
    simp only [affinePoint, Point.some.injEq]
    have e : ∀ z : ℂ, t * z + (s + c) = t * z + s + c := fun z ↦ by ring
    simp only [e, isPeriodic_weierstrassP _ c hc, isPeriodic_derivWeierstrassP _ c hc, and_self]
  · have hcp : constMap (weierstrassCurve L) MeroField (toPoint L c) =
        .some (germ fun _ ↦ ℘[L] c) (germ fun _ ↦ ℘'[L] c / 2)
          (equation_iff_nonsingular.1 (equation_germ (Meromorphic.const _) (Meromorphic.const _)
            (Eventually.of_forall fun _ ↦ equation_weierstrassP L hc))) := by
      rw [toPoint_of_notMem hc]
      show Point.some _ _ _ = Point.some _ _ _
      rw [Point.some.injEq]
      exact ⟨(germ_const _).symm, (germ_const _).symm⟩
    rw [hcp]
    apply add_some_germ (meromorphic_weierstrassP_affine L _ _)
      (meromorphic_derivWeierstrassP_half_affine L _ _) (Meromorphic.const _) (Meromorphic.const _)
      (meromorphic_weierstrassP_affine L _ _) (meromorphic_derivWeierstrassP_half_affine L _ _)
    · rw [germ_const]
      exact ne_algebraMap_of_transcendental (transcendental_germ_weierstrassP_affine L t s ht) _
    filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s,
      eventually_affine (eventually_notMem_lattice L) ht (s + c)] with z hz1 hz3
    have e : t * z + s + c = t * z + (s + c) := by ring
    refine ⟨equation_iff_nonsingular.1 (equation_weierstrassP L hz1),
      equation_iff_nonsingular.1 (equation_weierstrassP L hc),
      equation_iff_nonsingular.1 (equation_weierstrassP L hz3), ?_⟩
    have h := toPoint_add (L := L) (t * z + s) c
    rw [toPoint_of_notMem hz1, toPoint_of_notMem hc, e, toPoint_of_notMem hz3] at h
    exact h.symm

def ellEval : (weierstrassCurve L).toAffine.FunctionField →ₐ[ℂ] MeroField :=
  liftPoint (weierstrassCurve L) (equation_base L) (transcendental_germ_weierstrassP L)

theorem ellEval_genX : ellEval L (genX (weierstrassCurve L)) = germ ℘[L] :=
  liftPoint_genX _ _ _

theorem ellEval_genY : ellEval L (genY (weierstrassCurve L)) = germ fun z ↦ ℘'[L] z / 2 :=
  liftPoint_genY _ _ _

theorem ellEval_injective : Function.Injective (ellEval L) := (ellEval L).toRingHom.injective

theorem map_ellEval_genericPoint :
    Point.map (ellEval L) (genericPoint (weierstrassCurve L)) = basePoint L :=
  map_liftPoint_genericPoint _ _ _

theorem isEllipticFunction_derivWeierstrassP_half : IsEllipticFunction L fun z ↦ ℘'[L] z / 2 :=
  ⟨meromorphic_derivWeierstrassP_half L, fun z l hl ↦ by
    simp only [isPeriodic_derivWeierstrassP z l hl]⟩

theorem exists_isEllipticFunction_ellEval_eq (a : (weierstrassCurve L).toAffine.FunctionField) :
    ∃ f, IsEllipticFunction L f ∧ ellEval L a = germ f := by
  let S : IntermediateField ℂ (weierstrassCurve L).toAffine.FunctionField :=
    { carrier := {a | ∃ f, IsEllipticFunction L f ∧ ellEval L a = germ f}
      mul_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        refine ⟨f * g, ⟨hf.1.mul hg.1, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.mul_apply, hf.2 z l hl, hg.2 z l hl]
        · rw [map_mul, ha, hb, germ_mul hf.1 hg.1]
      one_mem' := ⟨fun _ ↦ 1, ⟨Meromorphic.const 1, fun _ _ _ ↦ rfl⟩, by
        rw [map_one, germ_const, map_one]⟩
      add_mem' := by
        rintro a b ⟨f, hf, ha⟩ ⟨g, hg, hb⟩
        refine ⟨f + g, ⟨hf.1.add hg.1, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.add_apply, hf.2 z l hl, hg.2 z l hl]
        · rw [map_add, ha, hb, germ_add hf.1 hg.1]
      zero_mem' := ⟨fun _ ↦ 0, ⟨Meromorphic.const 0, fun _ _ _ ↦ rfl⟩, by
        rw [map_zero, germ_const, map_zero]⟩
      algebraMap_mem' := fun c ↦ ⟨fun _ ↦ c, ⟨Meromorphic.const c, fun _ _ _ ↦ rfl⟩, by
        rw [AlgHom.commutes, germ_const]⟩
      inv_mem' := by
        rintro a ⟨f, hf, ha⟩
        refine ⟨f⁻¹, ⟨hf.1.inv, fun z l hl ↦ ?_⟩, ?_⟩
        · simp only [Pi.inv_apply, hf.2 z l hl]
        · rw [map_inv₀, ha, germ_inv hf.1] }
  have hX : genX (weierstrassCurve L) ∈ S :=
    ⟨℘[L], isEllipticFunction_weierstrassP (L := L), ellEval_genX L⟩
  have hY : genY (weierstrassCurve L) ∈ S :=
    ⟨_, isEllipticFunction_derivWeierstrassP_half L, ellEval_genY L⟩
  have hle : IntermediateField.adjoin ℂ {genX (weierstrassCurve L), genY (weierstrassCurve L)} ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with rfl | rfl
    · exact hX
    · exact hY
  rw [adjoin_genX_genY] at hle
  exact hle IntermediateField.mem_top

theorem exists_ellEval_eq_germ {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∃ a, ellEval L a = germ f := by
  obtain ⟨P, Q, R, S, hQ, hS, heq⟩ := exists_rational_weierstrassP hf
  have m℘ := L.meromorphic_weierstrassP
  have md := L.meromorphic_derivWeierstrassP
  have mP := meromorphic_eval_comp m℘ P
  have mQ := meromorphic_eval_comp m℘ Q
  have mR := meromorphic_eval_comp m℘ R
  have mS := meromorphic_eval_comp m℘ S
  have h2 : (2 : MeroField) * germ (fun z ↦ ℘'[L] z / 2) = germ ℘'[L] := by
    rw [show (fun z ↦ ℘'[L] z / 2) = ℘'[L] / fun _ ↦ (2 : ℂ) from rfl,
      germ_div md (Meromorphic.const 2), germ_const, map_ofNat]
    have h2ne : (2 : MeroField) ≠ 0 := by
      rw [← map_ofNat (algebraMap ℂ MeroField) 2]
      exact (_root_.map_ne_zero _).2 two_ne_zero
    exact mul_div_cancel₀ _ h2ne
  refine ⟨aeval (genX (weierstrassCurve L)) P / aeval (genX (weierstrassCurve L)) Q +
    2 * genY (weierstrassCurve L) * (aeval (genX (weierstrassCurve L)) R /
      aeval (genX (weierstrassCurve L)) S), ?_⟩
  rw [map_add, map_mul, map_mul, map_div₀, map_div₀, map_ofNat, ← aeval_algHom_apply,
    ← aeval_algHom_apply, ← aeval_algHom_apply, ← aeval_algHom_apply, ellEval_genX, ellEval_genY,
    h2, germ_aeval m℘ P, germ_aeval m℘ Q, germ_aeval m℘ R, germ_aeval m℘ S, ← germ_div mP mQ,
    ← germ_div mR mS, ← germ_mul md (mR.div mS), ← germ_add (mP.div mQ) (md.mul (mR.div mS))]
  exact (germ_congr hf.1 heq).symm

end Lattice

end Elliptic
end GroundTheory.Global
