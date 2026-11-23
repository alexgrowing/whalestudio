import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisionPoints
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdPt

open GlobalTheory.WeierstrassCurve in
theorem comp_pow_hom {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (ρ : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem equation_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    {W : _root_.WeierstrassCurve A} {x y : A} (h : W.toAffine.Equation x y) :
    (W.map f).toAffine.Equation (f x) (f y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  have := congrArg f h
  simpa only [map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using this

open GlobalTheory.WeierstrassCurve in

theorem exists_polAV_of_root (p : ℕ) {R C : Type} [CommRing R] [IsDomain R] [Field C] [Algebra R C]
    (hinj : Function.Injective (algebraMap R C)) (W : _root_.WeierstrassCurve R) (hΔ : IsUnit W.Δ)
    (x y : R) (hE : W.toAffine.Equation x y)
    (hψ : ((W.ΨSq p).map (algebraMap R C)).eval (algebraMap R C x) = 0) :
    ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (z : sp (R₀ := R) R ⟶ P.A), P.g = 1 ∧ z ^ p = 1 ∧
      ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1 := by
  classical
  haveI : W.IsElliptic := ⟨hΔ⟩
  obtain ⟨hA, hs, hL, hr, hsy, ha, hk⟩ := polarised_of_grpObj R W hΔ (isCommMonObj W) (one_left W)
  have hE' : (W.baseChange R).toAffine.Equation x y := by
    have : W.baseChange R = W := by simp [WeierstrassCurve.baseChange]
    rwa [this]
  have hU : IsUnimodularSol (W.baseChange R) ![x, y, 1] := isUnimodularSol_some hE'
  let z : sp (R₀ := R) R ⟶ schemeOver W := ptOver W ![x, y, 1] hU

  have hz : ∀ (k : Type) [Field k] [Algebra R k] (hk' : IsUnimodularSol (W.baseChange k)
      ![algebraMap R k x, algebraMap R k y, 1]),
      spMap (Algebra.ofId R k) ≫ z = ptOver W _ hk' := by
    intro k _ _ hk'
    refine Over.OverMorphism.ext ?_
    refine (SpecMap_pt W ![x, y, 1] hU (Algebra.ofId R k)).trans (pt_congr W _ _ ?_ hk')
    ext i; fin_cases i <;> simp [Algebra.ofId_apply]
  refine ⟨@Out.PolAV.mk _ (schemeOver W) (grpObj W) hA 1 hs (originLB W) hL hr hsy ha hk, z, rfl,
    ?_, ?_⟩
  · have hnz : (W.baseChange C).toAffine.Equation (algebraMap R C x) (algebraMap R C y) :=
      equation_map (algebraMap R C) hE
    have hns : (W.baseChange C).toAffine.Nonsingular (algebraMap R C x) (algebraMap R C y) :=
      (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hnz
    have hzero : (p : ℤ) • (WeierstrassCurve.Affine.Point.some _ _ hns) = 0 := by
      refine (GroundTheory.Arith.Abelian.zsmul_eq_zero_iff _ hns _).mpr ?_
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_ΨSq]
      exact hψ
    have hpt : (spMap (Algebra.ofId R C) ≫ z) ^ p = 1 := by
      rw [hz C (isUnimodularSol_some hnz), ← ofAffinePoint_some W hns, ← zpow_natCast,
        ← ofAffinePoint_zsmul, hzero, ofAffinePoint_zero, one_eq_zeroOver]
    have hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R C))) := by
      rw [isDominant_iff]
      show DenseRange (PrimeSpectrum.comap (algebraMap R C))
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R))
      (schemeOver W).hom ((Over.w _).trans (Over.w _).symm) (Spec.map (CommRingCat.ofHom (algebraMap R C))) ?_)
    have e := comp_pow_hom (spMap (Algebra.ofId R C)) z p
    rw [hpt, ← MonObj.comp_one (spMap (Algebra.ofId R C))] at e
    exact congrArg (·.left) e
  · intro k _ _ h
    have hk' : (W.baseChange k).toAffine.Equation (algebraMap R k x) (algebraMap R k y) :=
      equation_map (algebraMap R k) hE
    have hU' := isUnimodularSol_some hk'
    have h1 : spMap (Algebra.ofId R k) ≫ z = ptOver W _ hU' := hz k hU'
    have h2 := h1.symm.trans h
    rw [show (1 : sp (R₀ := R) k ⟶ schemeOver W) = _ from one_eq_ptOver W] at h2
    obtain ⟨u, hu⟩ := (ptOver_eq_ptOver_iff W _ _).mp h2
    have := congrFun hu 2
    simp at this
    exact u.ne_zero this.symm

end GlobalTheory.CompanionTheory.Ar.GR.OrdPt

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdPt

section Lucas

variable {F : Type} [Field F]

private theorem lucas_odd_key {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    (v ^ 2 * u ^ 5 - (v⁻¹) ^ 2 * (u⁻¹) ^ 5) * (u - u⁻¹) ^ 3 =
      (v * u ^ 4 - v⁻¹ * (u⁻¹) ^ 4) * (v * u ^ 2 - v⁻¹ * (u⁻¹) ^ 2) ^ 3 -
        (v * u - v⁻¹ * u⁻¹) * (v * u ^ 3 - v⁻¹ * (u⁻¹) ^ 3) ^ 3 := by
  field_simp
  ring

private theorem lucas_even_key {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    (v ^ 2 * u ^ 6 - (v⁻¹) ^ 2 * (u⁻¹) ^ 6) * (u ^ 2 - (u⁻¹) ^ 2) * (u - u⁻¹) ^ 2 =
      (v * u ^ 2 - v⁻¹ * (u⁻¹) ^ 2) ^ 2 * (v * u ^ 3 - v⁻¹ * (u⁻¹) ^ 3) *
          (v * u ^ 5 - v⁻¹ * (u⁻¹) ^ 5) -
        (v * u - v⁻¹ * u⁻¹) * (v * u ^ 3 - v⁻¹ * (u⁻¹) ^ 3) *
          (v * u ^ 4 - v⁻¹ * (u⁻¹) ^ 4) ^ 2 := by
  field_simp
  ring

theorem normEDS_lucas {u s b c d : F} (hu : u ≠ 0) (hs : s = u - u⁻¹) (hs0 : s ≠ 0) (hb0 : b ≠ 0)
    (hb : b = (u ^ 2 - (u⁻¹) ^ 2) / s ^ 4) (hc : c = (u ^ 3 - (u⁻¹) ^ 3) / s ^ 9)
    (hd : d * b = (u ^ 4 - (u⁻¹) ^ 4) / s ^ 16) (n : ℕ) :
    normEDS b c d (n : ℤ) = (u ^ n - (u⁻¹) ^ n) / s ^ (n ^ 2) := by
  induction n using normEDSRec with
  | zero => simp [normEDS_zero]
  | one =>
    simp only [Nat.cast_one, normEDS_one, pow_one, one_pow]
    rw [← hs, div_self hs0]
  | two => simpa using hb
  | three => simpa using hc
  | four => simpa using hd
  | even m h1 h2 h3 h4 h5 =>
    have hv : u ^ m ≠ 0 := pow_ne_zero _ hu
    have e := normEDS_even (b := b) (c := c) (d := d) ((m : ℤ) + 3)
    have c1 : ((m : ℤ) + 3 - 1) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    have c2 : ((m : ℤ) + 3) = ((m + 3 : ℕ) : ℤ) := by push_cast; ring
    have c3 : ((m : ℤ) + 3 + 2) = ((m + 5 : ℕ) : ℤ) := by push_cast; ring
    have c4 : ((m : ℤ) + 3 - 2) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have c5 : ((m : ℤ) + 3 + 1) = ((m + 4 : ℕ) : ℤ) := by push_cast; ring
    have c6 : 2 * ((m : ℤ) + 3) = ((2 * (m + 3) : ℕ) : ℤ) := by push_cast; ring
    rw [c1, c3, c4, c5, c6, c2, h1, h2, h3, h4, h5] at e
    refine mul_right_cancel₀ hb0 (e.trans ?_)
    have k := lucas_even_key hu hv
    have P : ∀ j : ℕ, u ^ (m + j) - (u⁻¹) ^ (m + j) = u ^ m * u ^ j - (u ^ m)⁻¹ * (u⁻¹) ^ j := by
      intro j; rw [pow_add, pow_add, inv_pow]
    have Q : u ^ (2 * (m + 3)) - (u⁻¹) ^ (2 * (m + 3)) =
        (u ^ m) ^ 2 * u ^ 6 - ((u ^ m)⁻¹) ^ 2 * (u⁻¹) ^ 6 := by
      rw [show 2 * (m + 3) = m * 2 + 6 by ring, pow_add, pow_add, pow_mul, pow_mul, inv_pow, inv_pow,
        inv_pow]
    rw [Q, P 1, P 2, P 3, P 4, P 5, pow_one, pow_one, hb]
    have D1 : (s ^ ((m + 2) ^ 2)) ^ 2 * s ^ ((m + 3) ^ 2) * s ^ ((m + 5) ^ 2) =
        s ^ ((2 * (m + 3)) ^ 2) * s ^ 4 * s ^ 2 := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
    have D2 : s ^ ((m + 1) ^ 2) * s ^ ((m + 3) ^ 2) * (s ^ ((m + 4) ^ 2)) ^ 2 =
        s ^ ((2 * (m + 3)) ^ 2) * s ^ 4 * s ^ 2 := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
    have T1 : ∀ a b c x y z : F, (a / x) ^ 2 * (b / y) * (c / z) = a ^ 2 * b * c / (x ^ 2 * y * z) := by
      intros; rw [div_pow, div_mul_div_comm, div_mul_div_comm]
    have T2 : ∀ a b c x y z : F, (a / x) * (b / y) * (c / z) ^ 2 = a * b * c ^ 2 / (x * y * z ^ 2) := by
      intros; rw [div_pow, div_mul_div_comm, div_mul_div_comm]
    rw [← hs] at k
    rw [T1, T2, D1, D2, ← sub_div, ← k, div_mul_div_comm]
    exact mul_div_mul_right _ _ (pow_ne_zero 2 hs0)
  | odd m h1 h2 h3 h4 =>
    have hv : u ^ m ≠ 0 := pow_ne_zero _ hu
    have e := normEDS_odd (b := b) (c := c) (d := d) ((m : ℤ) + 2)
    have c1 : ((m : ℤ) + 2 + 2) = ((m + 4 : ℕ) : ℤ) := by push_cast; ring
    have c2 : ((m : ℤ) + 2) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    have c3 : ((m : ℤ) + 2 - 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have c4 : ((m : ℤ) + 2 + 1) = ((m + 3 : ℕ) : ℤ) := by push_cast; ring
    have c5 : 2 * ((m : ℤ) + 2) + 1 = ((2 * (m + 2) + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [c1, c3, c4, c5, c2, h1, h2, h3, h4] at e
    refine e.trans ?_
    have k := lucas_odd_key hu hv
    have P : ∀ j : ℕ, u ^ (m + j) - (u⁻¹) ^ (m + j) = u ^ m * u ^ j - (u ^ m)⁻¹ * (u⁻¹) ^ j := by
      intro j; rw [pow_add, pow_add, inv_pow]
    have Q : u ^ (2 * (m + 2) + 1) - (u⁻¹) ^ (2 * (m + 2) + 1) =
        (u ^ m) ^ 2 * u ^ 5 - ((u ^ m)⁻¹) ^ 2 * (u⁻¹) ^ 5 := by
      rw [show 2 * (m + 2) + 1 = m * 2 + 5 by ring, pow_add, pow_add, pow_mul, pow_mul, inv_pow,
        inv_pow, inv_pow]
    rw [Q, P 1, P 2, P 3, P 4, pow_one, pow_one]
    have D1 : s ^ ((m + 4) ^ 2) * (s ^ ((m + 2) ^ 2)) ^ 3 = s ^ ((2 * (m + 2) + 1) ^ 2) * s ^ 3 := by
      rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    have D2 : s ^ ((m + 1) ^ 2) * (s ^ ((m + 3) ^ 2)) ^ 3 = s ^ ((2 * (m + 2) + 1) ^ 2) * s ^ 3 := by
      rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    have T : ∀ a b x y : F, (a / x) * (b / y) ^ 3 = a * b ^ 3 / (x * y ^ 3) := by
      intros; rw [div_pow, div_mul_div_comm]
    rw [← hs] at k
    rw [T, T, D1, D2, ← sub_div, ← k]
    exact mul_div_mul_right _ _ (pow_ne_zero 3 hs0)

end Lucas

end GlobalTheory.CompanionTheory.Ar.GR.OrdPt

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdPt

open Polynomial

def fam {A : Type} [CommRing A] (τ : A) : _root_.WeierstrassCurve A := ⟨1, 0, 0, 0, τ⟩

section Nodal

variable {k : Type} [Field k]

theorem ΨSq_eval_fam_zero (p : ℕ) [Fact p.Prime] [CharP k p] {u i s : k} (hui : u * i = 1)
    (hs : s = u - i) (hs0 : s ≠ 0) (hb : u + i ≠ 0) :
    ((fam (0 : k)).ΨSq p).eval ((s⁻¹) ^ 2) = ((s⁻¹) ^ 2) ^ (p ^ 2 - p) := by
  have hu : u ≠ 0 := left_ne_zero_of_mul_eq_one hui
  have hi : u⁻¹ = i := (eq_inv_of_mul_eq_one_right hui).symm
  have hE : (fam (0 : k)).toAffine.Equation ((s⁻¹) ^ 2) (i * (s⁻¹) ^ 3) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [fam]
    field_simp
    rw [hs]
    linear_combination hui
  have hb2 : (fam (0 : k)).b₂ = 1 := by simp [fam, WeierstrassCurve.b₂]
  have hb4 : (fam (0 : k)).b₄ = 0 := by simp [fam, WeierstrassCurve.b₄]
  have hb6 : (fam (0 : k)).b₆ = 0 := by simp [fam, WeierstrassCurve.b₆]
  have hb8 : (fam (0 : k)).b₈ = 0 := by simp [fam, WeierstrassCurve.b₈]
  have hB : 2 * (i * (s⁻¹) ^ 3) + (fam (0 : k)).a₁ * (s⁻¹) ^ 2 + (fam (0 : k)).a₃ =
      (u ^ 2 - (u⁻¹) ^ 2) / s ^ 4 := by
    simp only [fam, hi]
    field_simp
    rw [hs]
    ring
  have hb0 : 2 * (i * (s⁻¹) ^ 3) + (fam (0 : k)).a₁ * (s⁻¹) ^ 2 + (fam (0 : k)).a₃ ≠ 0 := by
    rw [hB, hi]
    refine div_ne_zero ?_ (pow_ne_zero _ hs0)
    have : u ^ 2 - i ^ 2 = s * (u + i) := by rw [hs]; ring
    rw [this]
    exact mul_ne_zero hs0 hb
  have hC : (fam (0 : k)).Ψ₃.eval ((s⁻¹) ^ 2) = (u ^ 3 - (u⁻¹) ^ 3) / s ^ 9 := by
    rw [GroundTheory.Arith.Abelian.Psi3_eval, hb2, hb4, hb6, hb8, hi]
    have : u ^ 3 - i ^ 3 = s * (s ^ 2 + 3) := by
      rw [hs]; linear_combination (3 * (u - i)) * hui
    rw [this]
    field_simp
    ring
  have hD : (fam (0 : k)).preΨ₄.eval ((s⁻¹) ^ 2) *
      (2 * (i * (s⁻¹) ^ 3) + (fam (0 : k)).a₁ * (s⁻¹) ^ 2 + (fam (0 : k)).a₃) =
      (u ^ 4 - (u⁻¹) ^ 4) / s ^ 16 := by
    rw [hB, GroundTheory.Arith.Abelian.prePsi4_eval, hb2, hb4, hb6, hb8, hi]
    have e4 : u ^ 4 - i ^ 4 = (u ^ 2 - i ^ 2) * (s ^ 2 + 2) := by
      rw [hs]; linear_combination (2 * (u ^ 2 - i ^ 2)) * hui
    rw [e4]
    field_simp
    ring
  have hL := normEDS_lucas hu (hi ▸ hs) hs0 hb0 hB hC hD p
  rw [← GroundTheory.Arith.Abelian.psiAt_sq _ hE, GroundTheory.Arith.Abelian.psiAt_eq, hL, hi,
    ← sub_pow_char u i, ← hs]
  obtain ⟨D, hD⟩ : ∃ D, p ^ 2 = p + D :=
    ⟨p ^ 2 - p, by have := Nat.le_self_pow (two_ne_zero) p; omega⟩
  rw [hD, Nat.add_sub_cancel_left, pow_add]
  have e : s ^ p / (s ^ p * s ^ D) = (s⁻¹) ^ D := by
    rw [inv_pow]
    field_simp
  rw [e, ← pow_mul, ← pow_mul, mul_comm]

theorem ΨSq_fam_zero (p : ℕ) [Fact p.Prime] [CharP k p] [IsAlgClosed k] :
    (fam (0 : k)).ΨSq p = X ^ (p ^ 2 - p) := by
  have key : ∀ x : k, x ≠ 0 → 4 * x + 1 ≠ 0 →
      ((fam (0 : k)).ΨSq p).eval x = (X ^ (p ^ 2 - p) : k[X]).eval x := by
    intro x hx h4
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_eq_mul_self (x⁻¹)
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact inv_ne_zero hx (by simpa using hw)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_root (X ^ 2 - C w * X - 1 : k[X]) (by
      have : (X ^ 2 - C w * X - 1 : k[X]).natDegree = 2 := by compute_degree!
      rw [degree_eq_natDegree (fun h => by simp [h] at this), this]
      norm_num)
    have hu' : u ^ 2 - w * u - 1 = 0 := by simpa [IsRoot] using hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hu'
    have hs : w = u - u⁻¹ := by
      field_simp
      linear_combination -hu'
    have hb : u + u⁻¹ ≠ 0 := by
      intro h
      have e : u⁻¹ = -u := by linear_combination h
      have e2 : w * w + 4 = 0 := by
        rw [hs, e]
        have : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
        rw [e] at this
        linear_combination (-4) * this
      apply h4
      have : x⁻¹ + 4 = 0 := by rw [hw]; exact e2
      field_simp at this
      linear_combination this
    have hx' : x = (w⁻¹) ^ 2 := by
      rw [inv_pow, pow_two, ← hw, inv_inv]
    have := ΨSq_eval_fam_zero p (mul_inv_cancel₀ hu0) hs hw0 hb
    rw [← hx'] at this
    simpa using this
  have h0 : (X * (C 4 * X + 1) * ((fam (0 : k)).ΨSq p - X ^ (p ^ 2 - p)) : k[X]) = 0 := by
    refine Polynomial.funext fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    by_cases h4 : 4 * x + 1 = 0
    · simp [h4]
    · rw [eval_mul, eval_sub, key x hx h4, sub_self, mul_zero, eval_zero]
  have hne : (X * (C 4 * X + 1) : k[X]) ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h => ?_
    have := congrArg (eval 0) h
    simp at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left hne)

end Nodal

end GlobalTheory.CompanionTheory.Ar.GR.OrdPt

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdPt

open Polynomial

section Root

variable {C : Type} [Field C] (v : Valuation C NNReal)

private theorem coeff_prod_lt (S : Multiset C) (hS : ∀ r ∈ S, 1 < v r) :
    v ((S.map fun r => X - Polynomial.C r).prod.coeff 0) ≠ 0 ∧
      ∀ d, 0 < d → v ((S.map fun r => X - Polynomial.C r).prod.coeff d) <
        v ((S.map fun r => X - Polynomial.C r).prod.coeff 0) := by
  induction S using Multiset.induction_on with
  | empty =>
    refine ⟨by simp, fun d hd => ?_⟩
    simp [Polynomial.coeff_one, hd.ne']
  | cons r S ih =>
    obtain ⟨h0, h1⟩ := ih fun r' h' => hS r' (Multiset.mem_cons_of_mem h')
    have hr : 1 < v r := hS r (Multiset.mem_cons_self r S)
    set h := (S.map fun r => X - Polynomial.C r).prod with hh
    have hpos : 0 < v (h.coeff 0) := pos_iff_ne_zero.mpr h0
    have hc0 : (((r ::ₘ S).map fun r => X - Polynomial.C r).prod).coeff 0 = -r * h.coeff 0 := by
      rw [Multiset.map_cons, Multiset.prod_cons, ← hh, sub_mul]
      simp [Polynomial.coeff_X_mul_zero]
    have hcd : ∀ d, (((r ::ₘ S).map fun r => X - Polynomial.C r).prod).coeff (d + 1) =
        h.coeff d - r * h.coeff (d + 1) := by
      intro d
      rw [Multiset.map_cons, Multiset.prod_cons, ← hh, sub_mul]
      simp [Polynomial.coeff_X_mul]
    have hv0 : v (-r * h.coeff 0) = v r * v (h.coeff 0) := by
      rw [map_mul, Valuation.map_neg]
    rw [hc0, hv0]
    refine ⟨mul_ne_zero (by positivity) h0, fun d hd => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    rw [Nat.succ_eq_add_one, hcd]
    have a1 : v (h.coeff d) ≤ v (h.coeff 0) := by
      rcases Nat.eq_zero_or_pos d with rfl | hd'
      · exact le_rfl
      · exact (h1 d hd').le
    have a2 : v (h.coeff 0) < v r * v (h.coeff 0) := lt_mul_of_one_lt_left hpos hr
    refine (Valuation.map_sub v _ _).trans_lt (max_lt (a1.trans_lt a2) ?_)
    rw [map_mul]
    exact mul_lt_mul_of_pos_left (h1 _ (Nat.succ_pos d)) (by positivity)

theorem exists_root_of_isUnit_coeff [IsAlgClosed C] {R : Type} [CommRing R] [Algebra R C]
    (hv : v.Integers R) (f : R[X]) {d : ℕ} (hd : 0 < d) (hu : IsUnit (f.coeff d)) :
    ∃ x : R, (f.map (algebraMap R C)).eval (algebraMap R C x) = 0 := by
  by_contra hno
  push_neg at hno
  set g := f.map (algebraMap R C) with hg
  have hgd : v (g.coeff d) = 1 := by
    rw [hg, Polynomial.coeff_map]
    exact hv.one_of_isUnit hu
  have hg0 : g ≠ 0 := by
    intro h
    rw [h] at hgd
    simp at hgd
  have hS : ∀ r ∈ g.roots, 1 < v r := by
    intro r hr
    by_contra hle
    obtain ⟨x, rfl⟩ := hv.exists_of_le_one (not_lt.mp hle)
    exact hno x ((mem_roots hg0).mp hr)
  obtain ⟨h0, h1⟩ := coeff_prod_lt v g.roots hS
  have hfac : Polynomial.C g.leadingCoeff * (g.roots.map fun r => X - Polynomial.C r).prod = g :=
    (IsAlgClosed.splits g).eq_prod_roots.symm
  have hlc : v g.leadingCoeff ≠ 0 := by
    simpa using hg0
  have e : ∀ j, v (g.coeff j) = v g.leadingCoeff *
      v ((g.roots.map fun r => X - Polynomial.C r).prod.coeff j) := by
    intro j
    conv_lhs => rw [← hfac, Polynomial.coeff_C_mul]
    rw [map_mul]
  have hlt : v (g.coeff d) < v (g.coeff 0) := by
    rw [e, e]
    exact mul_lt_mul_of_pos_left (h1 d hd) (pos_iff_ne_zero.mpr hlc)
  have hle : v (g.coeff 0) ≤ 1 := by
    rw [hg, Polynomial.coeff_map]
    exact hv.map_le_one _
  rw [hgd] at hlt
  exact absurd hlt (not_lt.mpr hle)

end Root

end GlobalTheory.CompanionTheory.Ar.GR.OrdPt

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdPt

open Polynomial IsLocalRing

theorem fam_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : A) :
    (fam t).map f = fam (f t) := by
  ext <;> simp [fam]

theorem Δ_fam {A : Type} [CommRing A] (t : A) : (fam t).Δ = -t - 432 * t ^ 2 := by
  simp [fam, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem exists_ordinary (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
    [CharP (ResidueField R) p] [IsAlgClosed (ResidueField R)] :
    ∃ t : R, IsUnit (fam t).Δ ∧ IsUnit (((fam t).ΨSq p).coeff (p ^ 2 - p)) := by
  set D := p ^ 2 - p with hD
  let c : (ResidueField R)[X] := ((fam (X : (ResidueField R)[X])).ΨSq p).coeff D
  have hev : ∀ τ : ResidueField R, c.eval τ = ((fam τ).ΨSq p).coeff D := by
    intro τ
    have e := WeierstrassCurve.map_ΨSq (fam (X : (ResidueField R)[X])) (evalRingHom τ) p
    rw [fam_map, coe_evalRingHom, eval_X] at e
    rw [e, Polynomial.coeff_map]
    rfl
  have hc0 : c.eval 0 = 1 := by
    rw [hev, ΨSq_fam_zero, ← hD, coeff_X_pow_self]
  have hc : c ≠ 0 := by
    intro h
    rw [h] at hc0
    simp at hc0
  have hq : (X * (Polynomial.C 432 * X + 1) : (ResidueField R)[X]) ≠ 0 := by
    refine mul_ne_zero X_ne_zero fun h => ?_
    have := congrArg (eval 0) h
    simp at this
  obtain ⟨τ, hτ⟩ : ∃ τ, (c * (X * (Polynomial.C 432 * X + 1))).eval τ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact mul_ne_zero hc hq (Polynomial.funext fun x => by simpa using hno x)
  rw [eval_mul] at hτ
  have hτ1 := left_ne_zero_of_mul hτ
  have hτ2 := right_ne_zero_of_mul hτ
  obtain ⟨t, rfl⟩ := residue_surjective τ
  refine ⟨t, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, ← WeierstrassCurve.map_Δ, fam_map, Δ_fam]
    intro h
    apply hτ2
    simp only [eval_mul, eval_X, eval_add, eval_C, eval_one]
    linear_combination -h
  · rw [← residue_ne_zero_iff_isUnit]
    rw [hev] at hτ1
    have e := WeierstrassCurve.map_ΨSq (fam t) (residue R) p
    rw [fam_map] at e
    rw [e, Polynomial.coeff_map] at hτ1
    exact hτ1

theorem isAlgClosed_residueField {C : Type} [Field C] [IsAlgClosed C] (v : Valuation C NNReal)
    {R : Type} [CommRing R] [Algebra R C] [IsLocalRing R] (hv : v.Integers R) :
    IsAlgClosed (ResidueField R) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨F, hF⟩ := Polynomial.map_surjective (residue R) residue_surjective f
  obtain ⟨G, hG, hdeg, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts _ |>.mpr ⟨F, hF⟩) hf
  have hpos : 0 < G.natDegree := hdeg ▸ hirr.natDegree_pos
  obtain ⟨x, hx⟩ := exists_root_of_isUnit_coeff v hv G hpos (by
    rw [coeff_natDegree, hmon.leadingCoeff]
    exact isUnit_one)
  rw [Polynomial.eval_map, eval₂_at_apply] at hx
  have h0 : G.eval x = 0 := hv.hom_inj (hx.trans (map_zero _).symm)
  refine ⟨residue R x, ?_⟩
  rw [← hG, Polynomial.eval_map, eval₂_at_apply, h0, map_zero]

end GlobalTheory.CompanionTheory.Ar.GR.OrdPt

open GlobalTheory.CompanionTheory.Ar.GR.OrdPt in

theorem GlobalTheory.CompanionTheory.Ar.GR.exists_ord_point : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → IsAdicComplete (Ideal.span {(p : R)}) R → ∃ (P : Out.PolAV (Spec (CommRingCat.of R))) (z : sp (R₀ := R) R ⟶ P.A), P.g = 1 ∧ z ^ p = 1 ∧ ∀ (k : Type) [Field k] [Algebra R k], spMap (Algebra.ofId R k) ≫ z ≠ 1 := by
  intro p _ C _ _ _ v R _ _ hv hp _
  have hinj := hv.hom_inj
  haveI : IsDomain R := hinj.isDomain (algebraMap R C)
  have hnon : ∀ a : R, a ∈ nonunits R ↔ v (algebraMap R C a) < 1 := fun a => by
    rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one a) h, fun h => h.ne⟩
  haveI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb => by
    rw [hnon] at ha hb ⊢
    rw [map_add]
    exact (Valuation.map_add v _ _).trans_lt (max_lt ha hb)
  haveI : IsAlgClosed (IsLocalRing.ResidueField R) := isAlgClosed_residueField v hv
  haveI : CharP (IsLocalRing.ResidueField R) p := by
    have h0 : ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := by
      rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]
      refine (hnon _).mpr ?_
      simpa using hp
    obtain ⟨q, hq⟩ := CharP.exists (IsLocalRing.ResidueField R)
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp ((CharP.cast_eq_zero_iff _ q p).mp h0) with rfl | rfl
    · have h1 := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) 1 1).mpr dvd_rfl
      rw [Nat.cast_one] at h1
      exact absurd h1 one_ne_zero
    · exact hq
  obtain ⟨t, hΔ, hc⟩ := exists_ordinary (R := R) p
  have hD : 0 < p ^ 2 - p := by
    have := (Fact.out : p.Prime).two_le
    have : p * 2 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨x, hx⟩ := exists_root_of_isUnit_coeff v hv _ hD hc
  let q : Polynomial R := Polynomial.X ^ 2 + Polynomial.C ((fam t).a₁ * x + (fam t).a₃) * Polynomial.X -
    Polynomial.C (x ^ 3 + (fam t).a₂ * x ^ 2 + (fam t).a₄ * x + (fam t).a₆)
  have hq2 : q.coeff 2 = 1 := by
    simp only [q]
    rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Polynomial.coeff_X]
    simp
  obtain ⟨y, hy⟩ := exists_root_of_isUnit_coeff v hv q two_pos (by rw [hq2]; exact isUnit_one)
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply] at hy
  have h0 : q.eval y = 0 := hinj (hy.trans (map_zero _).symm)
  have hE : (fam t).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [q, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h0
    linear_combination h0
  exact exists_polAV_of_root p hinj (fam t) hΔ x y hE hx
