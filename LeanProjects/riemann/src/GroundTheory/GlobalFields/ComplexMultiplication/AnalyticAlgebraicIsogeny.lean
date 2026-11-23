import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIndependent
import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicUnivAdd
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstant
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualWeil

open Filter Topology Set Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian KaehlerDifferential
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable (L₁ L₂ : PeriodPair)

def latticeHom : AddSubgroup ℂ where
  carrier := {α | ∀ l ∈ L₁.lattice, α * l ∈ L₂.lattice}
  add_mem' {a b} ha hb l hl := by
    rw [add_mul]
    exact add_mem (ha l hl) (hb l hl)
  zero_mem' l _ := by
    rw [zero_mul]
    exact zero_mem _
  neg_mem' {a} ha l hl := by
    rw [neg_mul]
    exact neg_mem (ha l hl)

variable {L₁ L₂}

theorem mem_latticeHom {α : ℂ} : α ∈ latticeHom L₁ L₂ ↔ ∀ l ∈ L₁.lattice, α * l ∈ L₂.lattice :=
  Iff.rfl

theorem meromorphicOrderAt_weierstrassP_affine (L : PeriodPair) {t s z₀ : ℂ} (ht : t ≠ 0)
    (hz : t * z₀ + s ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] (t * z + s)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ t * z + s) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ t * z + s) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul t).add_const s
    rw [h1.deriv, mul_one]
    exact ht
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

theorem germ_weierstrassP_ne (L : PeriodPair) {a b z₀ : ℂ} (ha : a ≠ 0)
    (h₁ : a * z₀ + 0 ∈ L.lattice) (h₂ : b * z₀ + 0 ∉ L.lattice) :
    (germ fun z ↦ ℘[L] (a * z + 0)) ≠ germ fun z ↦ ℘[L] (b * z + 0) := by
  intro h
  rw [germ_eq_germ_iff (meromorphic_weierstrassP_affine L a 0)
    (meromorphic_weierstrassP_affine L b 0)] at h
  have hne := (meromorphic_weierstrassP_affine L a 0 z₀).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
    (meromorphic_weierstrassP_affine L b 0 z₀) (mem_univ z₀) (by
      rw [accPt_iff_frequently_nhdsNE]
      exact Eventually.frequently (Eventually.of_forall fun _ ↦ mem_univ _)) h
  have h1 := meromorphicOrderAt_weierstrassP_affine L ha h₁
  rw [meromorphicOrderAt_congr hne] at h1
  have hf : AnalyticAt ℂ (fun z : ℂ ↦ b * z + 0) z₀ := by fun_prop
  have han : AnalyticAt ℂ (fun z ↦ ℘[L] (b * z + 0)) z₀ := by
    have h3 := AnalyticAt.comp (f := fun z : ℂ ↦ b * z + 0) (g := ℘[L])
      (L.analyticOnNhd_weierstrassP (b * z₀ + 0) h₂) hf
    exact h3
  have h0 := han.meromorphicOrderAt_nonneg
  rw [h1] at h0
  exact absurd h0 (by decide)

theorem sqrt_two_mul_notMem (L : PeriodPair) : (Real.sqrt 2 : ℂ) * L.ω₁ ∉ L.lattice := by
  intro h
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L h
  exact irrational_sqrt_two ⟨a, by push_cast; exact ha.symm⟩

theorem one_add_sqrt_two_ne_zero : (1 : ℂ) + Real.sqrt 2 ≠ 0 := by
  have : (0 : ℝ) < 1 + Real.sqrt 2 := by positivity
  exact_mod_cast this.ne'

theorem affinePoint_congr (L : PeriodPair) {t t' s s' : ℂ} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (e₁ : t = t') (e₂ : s = s') : affinePoint L t s ht = affinePoint L t' s' ht' := by
  subst e₁ e₂
  rfl

theorem basePoint_eq (L : PeriodPair) : basePoint L = affinePoint L 1 0 one_ne_zero := by
  simp only [basePoint, affinePoint, one_mul, add_zero]

theorem isGenPt_affinePoint (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    IsGenPt (weierstrassCurve L) (affinePoint L t s ht) :=
  transcendental_germ_weierstrassP_affine L t s ht

theorem genEval_affinePoint (L : PeriodPair) (s : ℂ) (hs : s ≠ 0)
    (h : IsGenPt (weierstrassCurve L) (affinePoint L s 0 hs)) :
    genEval (weierstrassCurve L) (affinePoint L s 0 hs) h = (affineComp s 0 hs).comp (ellEval L) := by
  refine (eq_genEval (weierstrassCurve L) _ ?_ h).symm
  rw [← Point.map_map, map_ellEval_genericPoint, map_affineComp_basePoint]

theorem isGenPt_of_map' {F : Type*} [Field F] {E : WeierstrassCurve F} {M N : Type*} [Field M]
    [Algebra F M] [DecidableEq M] [Field N] [Algebra F N] [DecidableEq N] (τ : M →ₐ[F] N)
    {A : (E.baseChange M).toAffine.Point} (h : IsGenPt E (Point.map τ A)) : IsGenPt E A := by
  cases A with
  | zero => exact h.elim
  | some x y k =>
    rw [Point.map_some, isGenPt_some] at h
    rw [isGenPt_some]
    exact fun halg ↦ h (halg.algHom τ)

theorem map_genEval_congr {F : Type*} [Field F] {E E' : WeierstrassCurve F} {M : Type*} [Field M]
    [Algebra F M] [DecidableEq M] (Q : (E'.baseChange E.toAffine.FunctionField).toAffine.Point)
    {P P' : (E.baseChange M).toAffine.Point} (e : P = P') (h : IsGenPt E P) (h' : IsGenPt E P') :
    Point.map (genEval E P h) Q = Point.map (genEval E P' h') Q := by
  subst e
  rfl

theorem isEllipticFunction_weierstrassP_mul {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    IsEllipticFunction L₁ fun z ↦ ℘[L₂] (α * z + 0) := by
  refine ⟨meromorphic_weierstrassP_affine L₂ α 0, fun z l hl ↦ ?_⟩
  show ℘[L₂] (α * (z + l) + 0) = ℘[L₂] (α * z + 0)
  rw [show α * (z + l) + 0 = (α * z + 0) + α * l by ring]
  exact isPeriodic_weierstrassP _ _ (hα l hl)

theorem isEllipticFunction_derivWeierstrassP_mul_half {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    IsEllipticFunction L₁ fun z ↦ ℘'[L₂] (α * z + 0) / 2 := by
  refine ⟨meromorphic_derivWeierstrassP_half_affine L₂ α 0, fun z l hl ↦ ?_⟩
  show ℘'[L₂] (α * (z + l) + 0) / 2 = ℘'[L₂] (α * z + 0) / 2
  rw [show α * (z + l) + 0 = (α * z + 0) + α * l by ring]
  simp only [isPeriodic_derivWeierstrassP _ _ (hα l hl)]

def isogX {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) : (weierstrassCurve L₁).toAffine.FunctionField :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_weierstrassP_mul hα)).choose

def isogY {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) : (weierstrassCurve L₁).toAffine.FunctionField :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_derivWeierstrassP_mul_half hα)).choose

theorem ellEval_isogX {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    ellEval L₁ (isogX hα) = germ fun z ↦ ℘[L₂] (α * z + 0) :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_weierstrassP_mul hα)).choose_spec

theorem ellEval_isogY {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) :
    ellEval L₁ (isogY hα) = germ fun z ↦ ℘'[L₂] (α * z + 0) / 2 :=
  (exists_ellEval_eq_germ L₁ (isEllipticFunction_derivWeierstrassP_mul_half hα)).choose_spec

theorem nonsingular_isog {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    ((weierstrassCurve L₂).baseChange (weierstrassCurve L₁).toAffine.FunctionField).toAffine.Nonsingular
      (isogX hα) (isogY hα) := by
  rw [← (weierstrassCurve L₂).toAffine.baseChange_nonsingular (ellEval_injective L₁),
    ellEval_isogX, ellEval_isogY]
  exact equation_iff_nonsingular.1 (equation_affine L₂ α 0 h0)

def isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    ((weierstrassCurve L₂).baseChange (weierstrassCurve L₁).toAffine.FunctionField).toAffine.Point :=
  .some _ _ (nonsingular_isog hα h0)

theorem map_ellEval_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    Point.map (ellEval L₁) (isogPt hα h0) = affinePoint L₂ α 0 h0 := by
  simp only [isogPt, affinePoint, Point.map_some, Point.some.injEq]
  exact ⟨ellEval_isogX hα, ellEval_isogY hα⟩

theorem isGenPt_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    IsGenPt (weierstrassCurve L₂) (isogPt hα h0) := by
  apply isGenPt_of_map' (ellEval L₁)
  rw [map_ellEval_isogPt]
  exact isGenPt_affinePoint L₂ α 0 h0

theorem value_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) (s : ℂ) (hs : s ≠ 0)
    (h : IsGenPt (weierstrassCurve L₁) (affinePoint L₁ s 0 hs)) :
    Point.map (genEval (weierstrassCurve L₁) (affinePoint L₁ s 0 hs) h) (isogPt hα h0) =
      affinePoint L₂ (α * s) 0 (mul_ne_zero h0 hs) := by
  rw [genEval_affinePoint L₁ s hs h, ← Point.map_map, map_ellEval_isogPt,
    map_affineComp_affinePoint]
  exact affinePoint_congr L₂ _ _ rfl (by ring)

theorem respectsAdd_isogPt {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    RespectsAdd (weierstrassCurve L₁) (weierstrassCurve L₂) (isogPt hα h0) := by
  set r : ℂ := (Real.sqrt 2 : ℂ)
  have hr : r ≠ 0 := sqrt_two_ne_zero
  have hA := isGenPt_map_genericPoint (weierstrassCurve L₁) (ellEval L₁)
  have eA : Point.map (ellEval L₁) (genericPoint (weierstrassCurve L₁)) =
      affinePoint L₁ 1 0 one_ne_zero := by
    rw [map_ellEval_genericPoint, basePoint_eq]
  have hx₁ : (germ fun z ↦ ℘[L₁] (1 * z + 0)) ≠ germ fun z ↦ ℘[L₁] (r * z + 0) :=
    germ_weierstrassP_ne L₁ one_ne_zero (z₀ := L₁.ω₁) (by simpa using L₁.ω₁_mem_lattice)
      (by simpa using sqrt_two_mul_notMem L₁)
  have eAB : affinePoint L₁ 1 0 one_ne_zero + affinePoint L₁ r 0 hr =
      affinePoint L₁ (1 + r) 0 one_add_sqrt_two_ne_zero := by
    rw [affinePoint_add L₁ one_ne_zero hr one_add_sqrt_two_ne_zero hx₁]
    exact affinePoint_congr L₁ _ _ rfl (by ring)
  apply respectsAdd_of_univAdd
  refine univAdd_of_pair (isogPt hα h0) (ellEval L₁)
    (equation_iff_nonsingular.1 (equation_affine L₁ r 0 hr)) (ellEval_indep L₁) hA
    (isGenPt_affinePoint L₁ r 0 hr) (by
      change IsGenPt _ (Point.map (ellEval L₁) (genericPoint _) + affinePoint L₁ r 0 hr)
      rw [eA, eAB]
      exact isGenPt_affinePoint L₁ _ 0 _) ?_
  have eS : Point.map (ellEval L₁) (genericPoint (weierstrassCurve L₁)) + affinePoint L₁ r 0 hr =
      affinePoint L₁ (1 + r) 0 one_add_sqrt_two_ne_zero := by
    rw [eA, eAB]
  have hx₂ : (germ fun z ↦ ℘[L₂] (α * 1 * z + 0)) ≠ germ fun z ↦ ℘[L₂] (α * r * z + 0) := by
    refine germ_weierstrassP_ne L₂ (mul_ne_zero h0 one_ne_zero) (z₀ := L₂.ω₁ / α) ?_ ?_
    · rw [show α * 1 * (L₂.ω₁ / α) + 0 = L₂.ω₁ by field_simp; ring]
      exact L₂.ω₁_mem_lattice
    · rw [show α * r * (L₂.ω₁ / α) + 0 = r * L₂.ω₁ by field_simp; ring]
      exact sqrt_two_mul_notMem L₂
  have key : affinePoint L₂ (α * (1 + r)) 0 (mul_ne_zero h0 one_add_sqrt_two_ne_zero) =
      affinePoint L₂ (α * 1) 0 (mul_ne_zero h0 one_ne_zero) +
        affinePoint L₂ (α * r) 0 (mul_ne_zero h0 hr) := by
    rw [affinePoint_add L₂ _ _ (by rw [← mul_add]; exact mul_ne_zero h0 one_add_sqrt_two_ne_zero)
      hx₂]
    exact affinePoint_congr L₂ _ _ (by ring) (by ring)
  have v1 := value_isogPt hα h0 1 one_ne_zero (isGenPt_affinePoint L₁ 1 0 one_ne_zero)
  have vr := value_isogPt hα h0 r hr (isGenPt_affinePoint L₁ r 0 hr)
  have vs := value_isogPt hα h0 (1 + r) one_add_sqrt_two_ne_zero
    (isGenPt_affinePoint L₁ _ 0 one_add_sqrt_two_ne_zero)
  refine (map_genEval_congr _ eS _ (isGenPt_affinePoint L₁ _ 0 one_add_sqrt_two_ne_zero)).trans ?_
  refine vs.trans (key.trans ?_)
  rw [← v1, ← vr]
  congr 1
  exact map_genEval_congr _ eA.symm _ _

def latticeIsog {α : ℂ} (hα : α ∈ latticeHom L₁ L₂) (h0 : α ≠ 0) :
    Isogeny (weierstrassCurve L₁) (weierstrassCurve L₂) :=
  ⟨isogPt hα h0, (isIsogeny_iff _).2 ⟨isGenPt_isogPt hα h0, respectsAdd_isogPt hα h0⟩⟩

open Classical in

def latticeToHom (α : latticeHom L₁ L₂) : isogHom (weierstrassCurve L₁) (weierstrassCurve L₂) :=
  if h : (α : ℂ) = 0 then 0 else (latticeIsog α.2 h).toHom

theorem latticeToHom_of_ne_zero (α : latticeHom L₁ L₂) (h : (α : ℂ) ≠ 0) :
    (latticeToHom α).1 = isogPt α.2 h := by
  rw [latticeToHom, dif_neg h]
  rfl

theorem latticeToHom_of_eq_zero (α : latticeHom L₁ L₂) (h : (α : ℂ) = 0) : latticeToHom α = 0 := by
  rw [latticeToHom, dif_pos h]

def omegaDeriv : KaehlerDifferential ℂ MeroField →ₗ[MeroField] MeroField := germDeriv.liftKaehlerDifferential

theorem omegaDeriv_D (u : MeroField) : omegaDeriv (D ℂ MeroField u) = germDeriv u :=
  germDeriv.liftKaehlerDifferential_comp_D u

theorem two_mul_germ_half {f : ℂ → ℂ} (hf : Meromorphic f) :
    (2 : MeroField) * germ (fun z ↦ f z / 2) = germ f := by
  rw [show (fun z ↦ f z / 2) = f / fun _ ↦ (2 : ℂ) from rfl, germ_div hf (Meromorphic.const 2),
    germ_const, map_ofNat]
  have h2ne : (2 : MeroField) ≠ 0 := by
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  exact mul_div_cancel₀ _ h2ne

theorem germ_derivWeierstrassP_half_ne_zero (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    (germ fun z ↦ ℘'[L] (t * z + s) / 2) ≠ 0 := by
  intro h
  have e := (equation_iff _ _).1 (equation_affine L t s ht)
  rw [h] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    weierstrassCurve_a₁, weierstrassCurve_a₂, weierstrassCurve_a₃, weierstrassCurve_a₄,
    weierstrassCurve_a₆, map_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero] at e
  apply transcendental_germ_weierstrassP_affine L t s ht
  refine ⟨X ^ 3 + C (-(L.g₂ / 4)) * X + C (-(L.g₃ / 4)), ?_, ?_⟩
  · apply_fun (fun p ↦ p.coeff 3)
    simp
  · simp only [map_add, map_pow, aeval_X, map_mul, aeval_C]
    linear_combination -e

theorem omegaDeriv_affinePoint (L : PeriodPair) (t s : ℂ) (ht : t ≠ 0) :
    omegaDeriv (omegaAt (weierstrassCurve L) (affinePoint L t s ht)) = algebraMap ℂ MeroField t := by
  obtain ⟨s₁, -⟩ := omegaAt_some_spec (weierstrassCurve L)
    (equation_iff_nonsingular.1 (equation_affine L t s ht))
  have e := congrArg omegaDeriv s₁
  rw [LinearMap.map_smul, omegaDeriv_D, germDeriv_germ (meromorphic_weierstrassP_affine L t s)] at e
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
    weierstrassCurve_a₁, weierstrassCurve_a₃, map_zero, zero_mul, add_zero, smul_eq_mul] at e
  have hd : deriv (fun z ↦ ℘[L] (t * z + s)) =ᶠ[codiscrete ℂ] fun z ↦ t * ℘'[L] (t * z + s) := by
    filter_upwards [eventually_affine (eventually_notMem_lattice L) ht s] with z hz
    have h1 := (hasDerivAt_weierstrassP hz).comp z (((hasDerivAt_id' z).const_mul t).add_const s)
    rw [mul_one] at h1
    rw [show (fun z ↦ ℘[L] (t * z + s)) = ℘[L] ∘ fun x ↦ t * x + s from rfl, h1.deriv, mul_comm]
  have md : Meromorphic fun z ↦ t * ℘'[L] (t * z + s) := fun x ↦
    (MeromorphicAt.const t x).mul (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s x)
  rw [germ_congr (meromorphic_weierstrassP_affine L t s).deriv hd,
    show (fun z ↦ t * ℘'[L] (t * z + s)) = (fun _ ↦ t) * fun z ↦ ℘'[L] (t * z + s) from rfl,
    germ_mul (Meromorphic.const t) (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s),
    germ_const, ← two_mul_germ_half (meromorphic_comp_affine L.meromorphic_derivWeierstrassP t s)] at e
  have hy := germ_derivWeierstrassP_half_ne_zero L t s ht
  have h2 : (2 : MeroField) * germ (fun z ↦ ℘'[L] (t * z + s) / 2) ≠ 0 := by
    refine mul_ne_zero ?_ hy
    rw [← map_ofNat (algebraMap ℂ MeroField) 2]
    exact (_root_.map_ne_zero _).2 two_ne_zero
  apply mul_left_cancel₀ h2
  exact e.trans (mul_comm _ _)

theorem kpush_const_smul {K M : Type*} [Field K] [Algebra ℂ K] [Field M] [Algebra ℂ M]
    (σ : K →ₐ[ℂ] M) (c : ℂ) (η : KaehlerDifferential ℂ K) : kpush σ (c • η) = c • kpush σ η := by
  rw [← algebraMap_smul K c η, kpush_smul, AlgHom.commutes, algebraMap_smul]

theorem homConst_latticeToHom (α : latticeHom L₁ L₂) :
    homConst (weierstrassCurve L₁) (weierstrassCurve L₂) (latticeToHom α) = α := by
  by_cases h0 : (α : ℂ) = 0
  · rw [latticeToHom_of_eq_zero α h0, map_zero, h0]
  have e := omegaAt_eq_homConst_smul (latticeToHom α)
  have e' := congrArg (kpush (ellEval L₁)) e
  rw [kpush_omegaAt, latticeToHom_of_ne_zero α h0, map_ellEval_isogPt, kpush_const_smul,
    invariantDifferential, kpush_omegaAt, map_ellEval_genericPoint, basePoint_eq] at e'
  have e'' := congrArg omegaDeriv e'
  rw [omegaDeriv_affinePoint, ← algebraMap_smul MeroField, LinearMap.map_smul,
    omegaDeriv_affinePoint, smul_eq_mul, map_one, mul_one] at e''
  exact ((algebraMap ℂ MeroField).injective e'').symm

end Elliptic
end GroundTheory.Global
