import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.BaseChangeDescent
import GroundTheory.GlobalFields.ComplexMultiplication.AutCFixed
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField

namespace GroundTheory.Global

open Polynomial WeierstrassCurve IntermediateField GroundTheory.Arith.Abelian
open WeierstrassCurve.Affine (Point equation_iff)

universe u

section Conj

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

variable (E) in

theorem baseChange_map_algEquiv (g : Ω ≃ₐ[F] Ω) :
    (E.baseChange Ω).map (g : Ω →+* Ω) = E.baseChange Ω :=
  WeierstrassCurve.map_baseChange (R := F) (S := F) E (g : Ω →ₐ[F] Ω)

noncomputable def _root_.GroundTheory.Arith.Abelian.Isogeny.conj (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    Isogeny (E.baseChange Ω) (E'.baseChange Ω) :=
  ψ.mapOf (g : Ω →+* Ω) (baseChange_map_algEquiv E g) (baseChange_map_algEquiv E' g)

variable (E) in
theorem ffCongr_ffMap_eq_galFF (g : Ω ≃ₐ[F] Ω) (f : (E.baseChange Ω).toAffine.FunctionField) :
    ffCongr (baseChange_map_algEquiv E g) (ffMap (g : Ω →+* Ω) (E.baseChange Ω) f) =
      galFF E g f := by
  have e : (ffCongr (baseChange_map_algEquiv E g)).toRingHom.comp
      (ffMap (g : Ω →+* Ω) (E.baseChange Ω)) = (galFF E g).toRingHom := by
    apply ringHom_ext_functionField
    · intro c
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        ffMap_algebraMap, ffCongr_algebraMap, galFF_algebraMap]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genX,
        ffCongr_genX, galFF_genX]
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ffMap_genY,
        ffCongr_genY, galFF_genY]
  exact DFunLike.congr_fun e f

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_alt_bis (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).x = galFF E g ψ.x := by
  rw [Isogeny.conj, Isogeny.mapOf_alt, ffCongr_ffMap_eq_galFF]

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_y (g : Ω ≃ₐ[F] Ω)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : (ψ.conj g).y = galFF E g ψ.y := by
  rw [Isogeny.conj, Isogeny.mapOf_y, ffCongr_ffMap_eq_galFF]

variable (E E') in

theorem map_galFF_curve' (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).map
      (galFF E g : _ →+* _) =
      (E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField := by
  have e : ∀ a : F, galFF E g (algebraMap Ω (E.baseChange Ω).toAffine.FunctionField
      (algebraMap F Ω a)) = algebraMap Ω _ (algebraMap F Ω a) := fun a => by
    rw [galFF_algebraMap, AlgEquiv.commutes]
  ext <;> exact e _

variable (E E') in

noncomputable def galPt (g : Ω ≃ₐ[F] Ω) :
    ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point →+
      ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point :=
  autPoint _ (galFF E g) (map_galFF_curve' E E' g)

theorem galPt_val (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) :
    galPt E E' g ψ.1 = (ψ.conj g).1 := by
  rw [ψ.val_eq, galPt, autPoint_some, (ψ.conj g).val_eq]
  exact point_some_congr (ψ.conj_alt_bis g).symm (ψ.conj_y g).symm

theorem galPt_constMap [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω) (c : (E'.baseChange Ω).toAffine.Point) :
    galPt E E' g (constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField c) =
      constMap (E'.baseChange Ω) (E.baseChange Ω).toAffine.FunctionField
        (galPointsHom F Ω E' g c) := by
  cases c with
  | zero => rfl
  | some x y h =>
    show autPoint _ _ _ (Point.some _ _ _) = Point.some _ _ _
    rw [autPoint_some]
    exact point_some_congr (galFF_algebraMap E g x) (galFF_algebraMap E g y)

theorem galPt_map_translate [IsAlgClosed Ω] [DecidableEq Ω] (g : Ω ≃ₐ[F] Ω)
    (R : (E.baseChange Ω).toAffine.Point)
    (Q : ((E'.baseChange Ω).baseChange (E.baseChange Ω).toAffine.FunctionField).toAffine.Point) :
    galPt E E' g (Point.map (translate (E.baseChange Ω) R) Q) =
      Point.map (translate (E.baseChange Ω) (galPointsHom F Ω E g R)) (galPt E E' g Q) := by
  cases Q with
  | zero => rfl
  | some a b h =>
    rw [Point.map_some, galPt, autPoint_some, autPoint_some, Point.map_some]
    exact point_some_congr (galFF_translate E g R a) (galFF_translate E g R b)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.pointMap_conj [IsAlgClosed Ω] [DecidableEq Ω]
    (g : Ω ≃ₐ[F] Ω) (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω))
    (R : (E.baseChange Ω).toAffine.Point) :
    (ψ.conj g).pointMap (galPointsHom F Ω E g R) = galPointsHom F Ω E' g (ψ.pointMap R) := by
  apply Isogeny.pointMap_eq_of_map_translate
  have h := congrArg (galPt E E' g) (ψ.map_translate R)
  rw [galPt_map_translate, map_add, galPt_val, galPt_constMap] at h
  exact h

end Conj

section Torsion

variable {F Ω : Type u} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]
variable {E E' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic]

theorem isAlgebraic_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (h : (E.baseChange Ω).toAffine.Nonsingular x y)
    (hR : n • (Point.some x y h : (E.baseChange Ω).toAffine.Point) = 0) :
    IsAlgebraic F x ∧ IsAlgebraic F y := by
  have hx : IsAlgebraic F x := by
    rcases (zsmul_eq_zero_iff_ΨSq (E.baseChange Ω) n _).mp hR with h0 | ⟨x', y', h', he, hev⟩
    · exact absurd h0 (Point.some_ne_zero h)
    · have hxx : x = x' := (Point.some.inj he).1
      refine ⟨E.ΨSq n, ΨSq_ne_zero_of_ne_zero E hn, ?_⟩
      rw [hxx, ← eval_map_algebraMap, ← WeierstrassCurve.map_ΨSq]
      exact hev
  refine ⟨hx, ?_⟩
  have hxi : IsIntegral F x := hx.isIntegral
  set A := integralClosure F Ω
  have hb : _root_.IsIntegral F (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) :=
    (isIntegral_algebraMap.mul hxi).add isIntegral_algebraMap
  have hc : _root_.IsIntegral F (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x +
      algebraMap F Ω E.a₆) :=
    (((hxi.pow 3).add (isIntegral_algebraMap.mul (hxi.pow 2))).add
      (isIntegral_algebraMap.mul hxi)).add isIntegral_algebraMap
  let b : A := ⟨_, hb⟩
  let c : A := ⟨_, hc⟩
  let q : A[X] := X ^ 2 + C b * X - C c
  have hmon : q.Monic := by
    simp only [q]
    monicity!
  have heq : aeval y q = 0 := by
    have e := (equation_iff _ _).mp h.1
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
    simp only [q, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
    show y ^ 2 + (algebraMap F Ω E.a₁ * x + algebraMap F Ω E.a₃) * y -
      (x ^ 3 + algebraMap F Ω E.a₂ * x ^ 2 + algebraMap F Ω E.a₄ * x + algebraMap F Ω E.a₆) = 0
    linear_combination e
  exact (isIntegral_trans (R := F) (A := A) y ⟨q, hmon, heq⟩).isAlgebraic

theorem galPointsHom_eq_self_of_zsmul_eq_zero (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z) {n : ℤ} (hn : n ≠ 0)
    {R : (E.baseChange Ω).toAffine.Point} (hR : n • R = 0) : galPointsHom F Ω E g R = R := by
  cases R with
  | zero => exact map_zero _
  | some x y h =>
    obtain ⟨hx, hy⟩ := isAlgebraic_of_zsmul_eq_zero hn h hR
    exact galPointsHom_some_eq_self F Ω E h (hg x hx) (hg y hy)

theorem _root_.GroundTheory.Arith.Abelian.Isogeny.conj_eq_self [IsAlgClosed Ω] (g : Ω ≃ₐ[F] Ω)
    (hg : ∀ z : Ω, IsAlgebraic F z → g z = z)
    (ψ : Isogeny (E.baseChange Ω) (E'.baseChange Ω)) : ψ.conj g = ψ := by
  have hfix : ∀ {n : ℤ}, n ≠ 0 → ∀ R : (E.baseChange Ω).toAffine.Point, n • R = 0 →
      (ψ.conj g).pointMap R = ψ.pointMap R := by
    intro n hn R hR
    have h1 := ψ.pointMap_conj g R
    rw [galPointsHom_eq_self_of_zsmul_eq_zero g hg hn hR] at h1
    rw [h1]
    apply galPointsHom_eq_self_of_zsmul_eq_zero g hg hn
    rw [← Isogeny.pointHom_apply, ← map_zsmul, hR, map_zero]
  set χ := (ψ.conj g).1 - ψ.1 with hχ
  have hmem : χ ∈ isogHom (E.baseChange Ω) (E'.baseChange Ω) :=
    (isogHom _ _).sub_mem (ψ.conj g).respectsAdd ψ.respectsAdd
  by_contra hne
  have hχ0 : (⟨χ, hmem⟩ : isogHom (E.baseChange Ω) (E'.baseChange Ω)) ≠ 0 := by
    intro h0
    apply hne
    apply Isogeny.ext'
    have h0' := congrArg Subtype.val h0
    exact sub_eq_zero.mp h0'
  set φχ := isogOfHom ⟨χ, hmem⟩ hχ0
  have hker : ∀ {n : ℤ}, n ≠ 0 → ∀ R, n • R = 0 → R ∈ φχ.pointHom.ker := by
    intro n hn R hR
    rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply]
    apply Isogeny.pointMap_eq_of_map_translate
    rw [isogOfHom_val, map_zero, add_zero]
    show Point.map _ ((ψ.conj g).1 - ψ.1) = (ψ.conj g).1 - ψ.1
    rw [map_sub, Isogeny.map_translate, Isogeny.map_translate, hfix hn R hR]
    abel
  obtain ⟨ℓ, hℓ2, hℓ⟩ : ∃ ℓ : ℕ, 2 ≤ ℓ ∧ (ℓ : Ω) ≠ 0 := by
    by_cases h2 : ((2 : ℕ) : Ω) = 0
    · refine ⟨3, by norm_num, ?_⟩
      have e : ((3 : ℕ) : Ω) = ((2 : ℕ) : Ω) + 1 := by push_cast; ring
      rw [e, h2, zero_add]
      exact one_ne_zero
    · exact ⟨2, le_refl 2, h2⟩
  set d := φχ.degree
  set n : ℤ := (ℓ : ℤ) ^ (d + 1) with hn
  have hnΩ : (n : Ω) ≠ 0 := by
    rw [hn]
    push_cast
    exact pow_ne_zero _ hℓ
  have hn0 : n ≠ 0 := fun h => hnΩ (by rw [h, Int.cast_zero])
  have hcard := card_zsmul_eq_zero (E.baseChange Ω) hnΩ
  have hle : Nat.card {P : (E.baseChange Ω).toAffine.Point // n • P = 0} ≤
      Nat.card φχ.pointHom.ker :=
    Nat.card_le_card_of_injective (fun P => ⟨P.1, hker hn0 P.1 P.2⟩)
      (by intro a b h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)
  have hkd := φχ.card_ker_le_degree
  have hnat : n.natAbs = ℓ ^ (d + 1) := by
    rw [hn, Int.natAbs_pow, Int.natAbs_natCast]
  rw [hcard, hnat] at hle
  have h2 : d < 2 ^ (d + 1) := (Nat.lt_two_pow_self).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (d + 1) ≤ ℓ ^ (d + 1) := Nat.pow_le_pow_left hℓ2 _
  have h4 : ℓ ^ (d + 1) ≤ (ℓ ^ (d + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  omega

end Torsion

end GroundTheory.Global
