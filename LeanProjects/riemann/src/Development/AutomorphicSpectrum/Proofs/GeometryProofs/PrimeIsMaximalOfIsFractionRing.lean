import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import GroundTheory.HeightsAndTheta.Heights.Intersections.OneNotMemOfIsPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveVerticalPointChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointResidue
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ExistsAlgPtOff
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg

section
open MvPolynomial GroundTheory.FunctionField
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (mem_of_aeval_eq chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_zero homog_X)

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

def Dom (v : Place (ZMod p) K) (w : (Σ k, J k) → K) (W : Ideal (MRing J)) : Prop :=
  ∀ (e : B → ℕ) (g h : MRing J), IsMultiHomog g e → IsMultiHomog h e → h ∉ W →
    v.valuation (aeval w g) ≤ v.valuation (aeval w h) ∧
      (g ∈ W → v.valuation (aeval w g) < v.valuation (aeval w h))

omit [Fact p.Prime] in
theorem X_mem_iff {K : Type} [Field K] (w : (Σ k, J k) → K) (k : B) (i : J k) :
    (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal w ↔ w ⟨k, i⟩ = 0 := by
  simp [mCoordIdeal, RingHom.mem_ker, mConeMap]

variable {v : Place (ZMod p) K} {w : (Σ k, J k) → K} {W W' : Ideal (MRing J)}

theorem Dom.le_chart (hD : Dom v w W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) (i : J k) :
    v.valuation (w ⟨k, i⟩) ≤ v.valuation (w ⟨k, c k⟩) := by
  classical
  simpa using (hD (Pi.single k 1) (X ⟨k, i⟩) (X ⟨k, c k⟩) (homog_X k i) (homog_X k (c k)) (hc k)).1

theorem Dom.sup_eq (hD : Dom v w W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) = v.valuation (w ⟨k, c k⟩) :=
  le_antisymm (Finset.sup_le fun i _ => hD.le_chart hc k i)
    (Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ _))

theorem Dom.lt_chart (hD : Dom v w W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) {i : J k}
    (hi : (X ⟨k, i⟩ : MRing J) ∈ W) : v.valuation (w ⟨k, i⟩) < v.valuation (w ⟨k, c k⟩) := by
  classical
  simpa using (hD (Pi.single k 1) (X ⟨k, i⟩) (X ⟨k, c k⟩) (homog_X k i) (homog_X k (c k)) (hc k)).2 hi

theorem Dom.le_of_dom (hD : Dom v w W) (hD' : Dom v w W') (hW : IsMultiHomogIdeal W) (hWp : W.IsPrime)
    {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) : W ≤ W' := by
  obtain ⟨S, hS, hSe⟩ := hW
  have hSW : Ideal.span S ≤ W := hSe.ge
  rw [hSe, Ideal.span_le]
  intro f hf
  obtain ⟨e, he⟩ := hS f hf
  by_contra hn
  have h1 := (hD e f (chartMono c e) he (isMultiHomog_chartMono c e) (chartMono_notMem hWp hc e)).2
    (hSW (Ideal.subset_span hf))
  have h2 := (hD' e (chartMono c e) f (isMultiHomog_chartMono c e) he hn).1
  exact absurd h1 (not_lt.2 h2)

end

section
open MvPolynomial GroundTheory.FunctionField

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
  {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem form_div_mem_chart {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) {g : MRing J} {d : B → ℕ}
    (hg : IsMultiHomog g d) : aeval w g * (∏ k, w ⟨k, c k⟩ ^ d k)⁻¹ ∈ chartRingZ w c := by
  rw [← GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue.aeval_div w c g d hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

omit [Fact p.Prime] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] in
theorem chart_isFractionRing (w : (Σ k, J k) → K) (hbir : Birational w) (c : ∀ k, J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ w c) K := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨d, g, h, hg, hh, h0, hz⟩ := hbir z
  have hm : (∏ k, w ⟨k, c k⟩ ^ d k)⁻¹ ≠ 0 :=
    inv_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_div_mem_chart w c hg⟩, ⟨_, form_div_mem_chart w c hh⟩, ?_⟩
  show z = aeval w g * _ / (aeval w h * _)
  rw [mul_div_mul_right _ _ hm, hz, mul_div_cancel_right₀ _ h0]

include p in
omit [Fintype B] [∀ k, Fintype (J k)] in

theorem prime_isMaximal_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [Algebra.FiniteType ℤ A] (q : Ideal A) (hq : q.IsPrime) (h0 : q ≠ ⊥) : q.IsMaximal := by
  have hpK : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hpA : CharP A p := (RingHom.charP_iff (algebraMap A K) (IsFractionRing.injective _ _) p).2 hpK
  letI : Algebra (ZMod p) A := ZMod.algebra _ p
  haveI : IsScalarTower (ZMod p) A K :=
    IsScalarTower.of_algebraMap_eq fun x =>
      DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
        ((algebraMap A K).comp (algebraMap (ZMod p) A))) x
  haveI : IsScalarTower ℤ (ZMod p) A := IsScalarTower.of_algebraMap_eq fun x => by simp
  haveI : Algebra.FiniteType (ZMod p) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
  have hd := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing (ZMod p) (A := A) K
  rw [GroundTheory.FunctionField.trdeg_eq_one] at hd
  have hle : Ring.KrullDimLE 1 A := by
    rw [Ring.krullDimLE_iff, hd]; simp
  exact Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hle q h0 hq

include p in

theorem chart_prime_isMaximal (w : (Σ k, J k) → K) (hbir : Birational w) (c : ∀ k, J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (q : Ideal (chartRingZ w c)) (hq : q.IsPrime) (h0 : q ≠ ⊥) : q.IsMaximal := by
  have hfr := chart_isFractionRing w hbir c hc
  haveI : Algebra.FiniteType ℤ (chartRingZ w c) := by
    refine (Subalgebra.fg_iff_finiteType _).1 ?_
    exact Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩
  exact prime_isMaximal_of_isFractionRing (p := p) (K := K) _ q hq h0

end

section
open MvPolynomial GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (mem_of_aeval_eq)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_zero mem_locRing_iff)

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]

def IsRho {K : Type} [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J))
    (ρ : locRing (mCoordIdeal w) W →+* K) : Prop :=
  ∀ (x : locRing (mCoordIdeal w) W) (u v : MRing J) (a : B → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (x : FractionRing (MRing J ⧸ mCoordIdeal w)) *
          algebraMap (MRing J ⧸ mCoordIdeal w) (FractionRing (MRing J ⧸ mCoordIdeal w)) (Ideal.Quotient.mk _ v) =
        algebraMap (MRing J ⧸ mCoordIdeal w) (FractionRing (MRing J ⧸ mCoordIdeal w)) (Ideal.Quotient.mk _ u) →
      ρ x * aeval w v = aeval w u

theorem exists_rho {K : Type} [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (hV : (mCoordIdeal w).IsPrime)
    (hW : W.IsPrime) (hVW : mCoordIdeal w ≤ W) : ∃ ρ, IsRho w W ρ := by
  classical
  haveI := hV
  haveI := hW
  let R := MRing J ⧸ mCoordIdeal w
  let P := MvPolynomial B K
  let E := FractionRing P
  let ι0 : R →+* P := Ideal.Quotient.lift (mCoordIdeal w) (mConeMap w : MRing J →+* P) (fun a ha => ha)
  have hι0 : Function.Injective ι0 := RingHom.lift_injective_of_ker_le_ideal _ _ (le_refl _)
  let ι : R →+* E := (algebraMap P E).comp ι0
  have hι : Function.Injective ι := (IsFractionRing.injective P E).comp hι0
  let j : FractionRing R →+* E := IsFractionRing.lift hι
  let κ : K →+* E := (algebraMap P E).comp MvPolynomial.C
  have hκ : Function.Injective κ := (IsFractionRing.injective P E).comp (C_injective _ _)
  have hj : ∀ u, j (algebraMap R _ (Ideal.Quotient.mk _ u)) = algebraMap P E (mConeMap w u) := fun u => by
    simp [j, IsFractionRing.lift_algebraMap, ι, ι0]
    rfl
  have key : ∀ (x : locRing (mCoordIdeal w) W) (u v : MRing J) (a : B → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ W →
      (x : FractionRing R) * algebraMap R (FractionRing R) (Ideal.Quotient.mk _ v) =
        algebraMap R (FractionRing R) (Ideal.Quotient.mk _ u) →
      j x * κ (aeval w v) = κ (aeval w u) := by
    intro x u v a hu hv hvW hx
    have h1 := congrArg j hx
    rw [map_mul, hj, hj, GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form w hu,
      GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.mConeMap_form w hv, map_mul, map_mul] at h1
    have hT : algebraMap P E (∏ k, X k ^ a k) ≠ 0 := by
      intro h0
      have := IsFractionRing.injective P E (h0.trans (map_zero _).symm)
      exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) this
    apply mul_left_cancel₀ hT
    calc _ = j x * (algebraMap P E (∏ k, X k ^ a k) * algebraMap P E (C (aeval w v))) := by
          simp only [κ, RingHom.comp_apply]; ring
      _ = _ := h1
  have hv0 : ∀ {v : MRing J} {a : B → ℕ}, IsMultiHomog v a → v ∉ W → aeval w v ≠ 0 := fun {v a} hv hvW h0 =>
    hvW (mem_of_aeval_eq w hVW (homog_zero a) hv rfl (by simp [h0]) W.zero_mem)
  have hmem : ∀ x : locRing (mCoordIdeal w) W, j x ∈ κ.range := by
    intro x
    obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := (mem_locRing_iff hVW).1 x.2
    refine ⟨aeval w u / aeval w v, ?_⟩
    have h1 := key x u v a hu hv hvW hx
    have h2 : κ (aeval w v) ≠ 0 := fun h => hv0 hv hvW (hκ (h.trans (map_zero _).symm))
    rw [map_div₀, ← h1, mul_div_cancel_right₀ _ h2]
  let ρ0 : locRing (mCoordIdeal w) W →+* κ.range :=
    (j.comp (locRing (mCoordIdeal w) W).subtype).codRestrict κ.range (fun x => hmem x)
  let e : K ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b h => hκ (congrArg Subtype.val h), κ.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp ρ0, ?_⟩
  intro x u v a hu hv hvW hx
  have h3 : κ ((e.symm.toRingHom.comp ρ0) x) = j x := by
    have : e ((e.symm.toRingHom.comp ρ0) x) = ρ0 x := by simp
    exact congrArg Subtype.val this
  apply hκ
  rw [map_mul, h3]
  exact key x u v a hu hv hvW hx

end

section
open MvPolynomial GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (mem_of_aeval_eq chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_zero homog_X mem_locRing_iff div_mem_locRing fracHom fracHom_apply fracHom_eq_zero_iff isLocalRing mem_maximalIdeal_iff isUnit_iff)

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]

section
variable {K : Type} [Field K] {w : (Σ k, J k) → K} {W : Ideal (MRing J)}

theorem aeval_form_ne_zero (hVW : mCoordIdeal w ≤ W) {v : MRing J} {a : B → ℕ} (hv : IsMultiHomog v a) (hvW : v ∉ W) :
    aeval w v ≠ 0 := fun h0 =>
  hvW (mem_of_aeval_eq w hVW (homog_zero a) hv rfl (by simp [h0]) W.zero_mem)

theorem IsRho.div (hV : (mCoordIdeal w).IsPrime) (hW : W.IsPrime) (hVW : mCoordIdeal w ≤ W) {ρ} (hρ : IsRho w W ρ)
    {u v : MRing J} {a : B → ℕ} (hu : IsMultiHomog u a) (hv : IsMultiHomog v a) (hvW : v ∉ W) :
    ∃ x : locRing (mCoordIdeal w) W, (x : FractionRing (MRing J ⧸ mCoordIdeal w)) *
        algebraMap (MRing J ⧸ mCoordIdeal w) (FractionRing (MRing J ⧸ mCoordIdeal w)) (Ideal.Quotient.mk _ v) =
      algebraMap (MRing J ⧸ mCoordIdeal w) (FractionRing (MRing J ⧸ mCoordIdeal w)) (Ideal.Quotient.mk _ u) ∧
      ρ x * aeval w v = aeval w u := by
  haveI := hV
  haveI := hW
  have hv0 : fracHom (mCoordIdeal w) v ≠ 0 := fun h => hvW (hVW (fracHom_eq_zero_iff.1 h))
  have hx : (fracHom (mCoordIdeal w) u / fracHom (mCoordIdeal w) v) * fracHom (mCoordIdeal w) v = fracHom (mCoordIdeal w) u :=
    div_mul_cancel₀ _ hv0
  exact ⟨⟨_, div_mem_locRing hVW hu hv hvW⟩, hx, hρ _ u v a hu hv hvW hx⟩

theorem IsRho.injective (hV : (mCoordIdeal w).IsPrime) (hW : W.IsPrime) (hVW : mCoordIdeal w ≤ W) {ρ} (hρ : IsRho w W ρ) :
    Function.Injective ρ := by
  haveI := hV
  haveI := hW
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, v, a, hu, hv, hvW, hxu⟩ := (mem_locRing_iff hVW).1 x.2
  have h1 := hρ x u v a hu hv hvW hxu
  rw [hx, zero_mul] at h1
  have h2 : u ∈ mCoordIdeal w := mem_of_aeval_eq w le_rfl (homog_zero a) hu rfl (by simp [← h1]) (Ideal.zero_mem _)
  have hv0 : fracHom (mCoordIdeal w) v ≠ 0 := fun h => hvW (hVW (fracHom_eq_zero_iff.1 h))
  have h3 : (x : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) v = 0 := by
    rw [hxu]; exact fracHom_eq_zero_iff.2 h2
  exact Subtype.ext ((mul_eq_zero.1 h3).resolve_right hv0)

theorem IsRho.isFractionRing (hbir : Birational w) (hV : (mCoordIdeal w).IsPrime) (hW : W.IsPrime)
    (hVW : mCoordIdeal w ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) {ρ} (hρ : IsRho w W ρ) :
    letI := ρ.toAlgebra
    IsFractionRing (locRing (mCoordIdeal w) W) K := by
  letI := ρ.toAlgebra
  haveI : FaithfulSMul (locRing (mCoordIdeal w) W) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (hρ.injective hV hW hVW)
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨d, g, h, hg, hh, h0, hz⟩ := hbir z
  have hm := isMultiHomog_chartMono c d
  have hmW := chartMono_notMem hW hc d
  obtain ⟨x, -, hx⟩ := hρ.div hV hW hVW hg hm hmW
  obtain ⟨y, -, hy⟩ := hρ.div hV hW hVW hh hm hmW
  have hm0 := aeval_form_ne_zero hVW hm hmW
  refine ⟨x, y, ?_⟩
  show z = ρ x / ρ y
  have hy0 : ρ y ≠ 0 := fun h => h0 (by rw [← hy, h, zero_mul])
  rw [eq_div_iff hy0]
  apply mul_right_cancel₀ hm0
  rw [mul_assoc, hy, mul_comm _ (aeval w h), hx, hz, mul_comm]

end

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]
  {w : (Σ k, J k) → K} {W : Ideal (MRing J)}

theorem IsRho.dom_iff (hV : (mCoordIdeal w).IsPrime) (hW : W.IsPrime) (hVW : mCoordIdeal w ≤ W) {ρ} (hρ : IsRho w W ρ)
    [IsLocalRing (locRing (mCoordIdeal w) W)] (v : Place (ZMod p) K) :
    ((∀ a, v.valuation (ρ a) ≤ 1) ∧ ∀ a ∈ maximalIdeal (locRing (mCoordIdeal w) W), v.valuation (ρ a) < 1) ↔
      Dom v w W := by
  haveI := hV
  haveI := hW
  constructor
  · rintro ⟨h1, h2⟩ e g h hg hh hhW
    obtain ⟨x, hxf, hx⟩ := hρ.div hV hW hVW hg hh hhW
    have hh0 := aeval_form_ne_zero hVW hh hhW
    have hpos : 0 < v.valuation (aeval w h) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hh0)
    rw [← hx, map_mul]
    refine ⟨mul_le_of_le_one_left' (h1 x), fun hgW => ?_⟩
    have hm : x ∈ maximalIdeal (locRing (mCoordIdeal w) W) :=
      (mem_maximalIdeal_iff hVW x hg hh hhW hxf).2 hgW
    exact mul_lt_of_lt_one_left hpos (h2 x hm)
  · intro hD
    have gen : ∀ a : locRing (mCoordIdeal w) W, ∃ (u t : MRing J) (e : B → ℕ), IsMultiHomog u e ∧ IsMultiHomog t e ∧ t ∉ W ∧
        (a : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) t = fracHom (mCoordIdeal w) u :=
      fun a => (mem_locRing_iff hVW).1 a.2
    constructor
    · intro a
      obtain ⟨u, t, e, hu, ht, htW, ha⟩ := gen a
      have h1 := hρ a u t e hu ht htW ha
      have ht0 := aeval_form_ne_zero hVW ht htW
      have hpos : 0 < v.valuation (aeval w t) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0)
      have h2 := (hD e u t hu ht htW).1
      rw [← h1, map_mul] at h2
      exact le_of_mul_le_mul_right (by simpa using h2) hpos
    · intro a ham
      obtain ⟨u, t, e, hu, ht, htW, ha⟩ := gen a
      have h1 := hρ a u t e hu ht htW ha
      have ht0 := aeval_form_ne_zero hVW ht htW
      have hpos : 0 < v.valuation (aeval w t) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0)
      have huW : u ∈ W := (mem_maximalIdeal_iff hVW a hu ht htW ha).1 ham
      have h2 := (hD e u t hu ht htW).2 huW
      rw [← h1, map_mul] at h2
      exact lt_of_mul_lt_mul_right (by simpa using h2) (zero_le)

end

end GlobalTheory.CompanionTheory.Ar.GeoDeg
