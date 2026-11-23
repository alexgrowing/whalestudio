import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehomA
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.AwayToSectionFromZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin

namespace GlobalTheory

theorem coeff_eq_zero_of_simple_pole {R B C κ : Type*} [CommRing R] [CommRing B] [CommRing C]
    (ρ : R →+* B) (ι : B →+* C) (hι : Function.Injective ι) (ε : B →+* R)
    (hρ : ∀ r, ε (ρ r) = r) (z : B) (hz : ε z = 0) (d : κ → ℕ) (hd : Function.Injective d)
    (e : κ → C) (v : κ → B) (hv : ∀ k, ι z ^ d k * e k = ι (v k)) (hε : ∀ k, ε (v k) = 1)
    (c : κ → R) (s : Finset κ) (b : B) (h : ι z * ∑ k ∈ s, ι (ρ (c k)) * e k = ι b) :
    ∀ k ∈ s, 2 ≤ d k → c k = 0 := by
  classical
  induction s using Finset.induction_on_max_value d with
  | empty => simp
  | insert a s ha hmax ih =>
    by_cases h2 : 2 ≤ d a
    · have hlt : ∀ k ∈ s, d k < d a := fun k hk =>
        lt_of_le_of_ne (hmax k hk) fun e => ha (hd e ▸ hk)
      have key : ρ (c a) * v a + ∑ k ∈ s, ρ (c k) * (z ^ (d a - d k) * v k) = z ^ (d a - 1) * b := by
        apply hι
        rw [map_mul ι (z ^ _), ← h, map_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega),
          Finset.sum_insert ha, mul_add, map_add, map_sum, Finset.mul_sum, map_mul, ← hv]
        refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k hk => ?_)
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hlt k hk).le
        rw [map_mul, map_mul, map_pow, ← hv, hm, Nat.add_sub_cancel_left]
        ring
      have hca : c a = 0 := by
        have := congrArg ε key
        rw [map_add, map_sum, map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, hρ, hε,
          mul_one, Finset.sum_eq_zero, add_zero] at this
        · exact this
        · intro k hk
          have := hlt k hk
          rw [map_mul, map_mul, map_pow, hz, zero_pow (by omega), zero_mul, mul_zero]
      rw [Finset.sum_insert ha, hca, map_zero, map_zero, zero_mul, zero_add] at h
      intro k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact fun _ => hca
      · exact ih h k hk
    · intro k hk hk2
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact absurd hk2 h2
      · have := hmax k hk
        omega

namespace WeierstrassCurve

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

def constOn (U : (scheme W).Opens) : R →+* Γ(scheme W, U) := (baseRingHom (toSpec W) U).hom

theorem constOn_apply (U : (scheme W).Opens) (r : R) : constOn W U r = constFn (toSpec W) U r := rfl

def ratioOn (U : (scheme W).Opens) (i : Fin 3) (hU : U ≤ coordOpen W i) (j : Fin 3) :
    Γ(scheme W, U) :=
  frac (grading W) U (coord W j) (coord W i) (coord_mem W j) (coord_mem W i) hU

abbrev ratio (i j : Fin 3) : Γ(scheme W, coordOpen W i) := ratioOn W (coordOpen W i) i le_rfl j

section

variable {W} {U V : (scheme W).Opens} {i j k : Fin 3}

theorem resG_constOn (h : V ≤ U) (r : R) : resG _ h (constOn W U r) = constOn W V r :=
  baseRingHom_res (toSpec W) h r

theorem resG_ratioOn (hi : U ≤ coordOpen W i) (h : V ≤ U) :
    resG _ h (ratioOn W U i hi j) = ratioOn W V i (h.trans hi) j := rfl

@[simp] theorem ratioOn_self (hi : U ≤ coordOpen W i) : ratioOn W U i hi i = 1 := frac_self

theorem ratioOn_mul_ratioOn (hi : U ≤ coordOpen W i) (hj : U ≤ coordOpen W j) :
    ratioOn W U i hi j * ratioOn W U j hj k = ratioOn W U i hi k :=
  frac_mul_eq (by ring)

theorem isUnit_ratioOn (hi : U ≤ coordOpen W i) (hj : U ≤ coordOpen W j) :
    IsUnit (ratioOn W U i hi j) :=
  IsUnit.of_mul_eq_one _ ((ratioOn_mul_ratioOn hi hj).trans (ratioOn_self hi))

theorem basicOpen_ratioOn (hi : U ≤ coordOpen W i) :
    (scheme W).basicOpen (ratioOn W U i hi j) = U ⊓ coordOpen W j :=
  basicOpen_frac

end

def awayFnEquiv (i : Fin 3) : AwayRing W i ≃+* Γ(scheme W, coordOpen W i) :=
  (Proj.basicOpenIsoAway (grading W) (coord W i) (coord_mem W i) one_pos).commRingCatIsoToRingEquiv

@[simp] theorem awayFnEquiv_awayCoord (i j : Fin 3) :
    awayFnEquiv W i (awayCoord W i j) = ratio W i j :=
  (awayToSection_mk (coord_mem W i) 1 (coord_mem W j)).trans (frac_eq (by ring))

@[simp] theorem awayFnEquiv_awayConst (i : Fin 3) (r : R) :
    awayFnEquiv W i (awayConst W i r) = constOn W (coordOpen W i) r := by
  have h := baseRingHom_comp_SpecMap (Proj.toSpecZero (grading W))
    (CommRingCat.ofHom (algebraMap R (grading W 0))) (coordOpen W i)
  have h' := ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen (grading W) (coord_mem W i) one_pos
  exact (congrArg (fun φ => φ.hom r) (h.trans (congrArg (_ ≫ ·) h'))).symm

section

variable {W} {U : (scheme W).Opens} {i : Fin 3}

theorem equation_ratioOn (hi : U ≤ coordOpen W i) :
    (W.map (constOn W U)).toProjective.Equation (ratioOn W U i hi) := by
  have h := ((isUnimodularSol_awayCoord W i).map_comp
    ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _))).equation
  have e₁ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)).comp (awayConst W i) =
      constOn W U := RingHom.ext fun r =>
    (congrArg (resG _ hi) (awayFnEquiv_awayConst W i r)).trans (resG_constOn hi r)
  have e₂ : ((resG _ hi).comp (awayFnEquiv W i : AwayRing W i →+* _)) ∘ awayCoord W i =
      ratioOn W U i hi := funext fun j => congrArg (resG _ hi) (awayFnEquiv_awayCoord W i j)
  rwa [e₁, e₂] at h

end

theorem eval₂Hom_ratio_surjective (i : Fin 3) :
    Function.Surjective (MvPolynomial.eval₂Hom (constOn W (coordOpen W i)) (ratio W i)) := by
  intro a
  obtain ⟨a, rfl⟩ := (awayFnEquiv W i).surjective a
  obtain ⟨n, b, hb, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (grading W) (coord_mem W i) a
  rw [← evalHom_awayCoord]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨p, ?_⟩
  rw [evalHom_mk]
  have := MvPolynomial.eval₂_comp_left (awayFnEquiv W i).toRingHom (awayConst W i)
    (awayCoord W i) p
  refine Eq.trans ?_ this.symm
  rw [MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext fun r => (awayFnEquiv_awayConst W i r).symm
  · exact funext fun j => (awayFnEquiv_awayCoord W i j).symm

theorem SpecMap_awayFnEquiv_awayChart (i : Fin 3) :
    spMap (awayFnEquiv W i : AwayRing W i →+* Γ(scheme W, coordOpen W i)) ≫ awayChart W i =
      (isAffineOpen_coordOpen W i).fromSpec := by
  have h := Proj.basicOpenIsoSpec_hom (grading W) (coord W i) (coord_mem W i) one_pos
  have hU := Proj.isAffineOpen_basicOpen (grading W) (coord W i) (coord_mem W i) one_pos
  change Spec.map (Proj.awayToSection (grading W) (coord W i)) ≫
    Proj.awayι (grading W) (coord W i) (coord_mem W i) one_pos = hU.fromSpec
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, h, Iso.eq_inv_comp]
  rfl

theorem fromSpec_coordOpen_eq_ptHom (i : Fin 3) :
    (isAffineOpen_coordOpen W i).fromSpec = ptHom W (constOn W (coordOpen W i)) (ratio W i)
      (.of_isUnit (equation_ratioOn le_rfl) i (by simp)) := by
  rw [← SpecMap_awayFnEquiv_awayChart, SpecMap_awayChart]
  exact ptHom_congr W _ _ _ (RingHom.ext (awayFnEquiv_awayConst W i))
    (funext (awayFnEquiv_awayCoord W i)) _

section

variable {W} {A : Type} [CommRing A]

theorem evalPt_constOn {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : evalPt x U h (constOn W U r) = ρ r := by
  rw [constOn_apply, evalPt_constFn]
  exact (congrArg (fun y : Sp A ⟶ Sp R => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hx).trans (evalPt_spMap _ r)

theorem eq_ptHom_evalPt {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ x ⁻¹ᵁ U)
    {P : Fin 3 → A} (hP : ∀ j, evalPt x U h (ratioOn W U i hi j) = P j) :
    ∃ hP, x = ptHom W ρ P hP := by
  have h' : ⊤ ≤ x ⁻¹ᵁ coordOpen W i := h.trans (x.preimage_mono hi)
  have e := eq_spec_fromSpec (isAffineOpen_coordOpen W i) x h'
  rw [fromSpec_coordOpen_eq_ptHom, SpecMap_ptHom] at e
  have e₁ : (evalPt x _ h').comp (constOn W _) = ρ := RingHom.ext (evalPt_constOn hx h')
  have e₂ : evalPt x _ h' ∘ ratio W i = P := funext fun j =>
    (evalPt_res x hi h' h _).symm.trans (hP j)
  subst e₁ e₂
  exact ⟨_, e⟩

theorem evalPt_ptHom_ratioOn_mul (ρ : R →+* A) (P : Fin 3 → A) (hP : IsUnimodularSol (W.map ρ) P)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ U)
    (j : Fin 3) : evalPt (ptHom W ρ P hP) U h (ratioOn W U i hi j) * P i = P j := by
  have h' : ⊤ ≤ ptHom W ρ P hP ⁻¹ᵁ coordOpen W i := h.trans ((ptHom W ρ P hP).preimage_mono hi)
  have hu : IsUnit (P i) := by
    rw [ptHom_preimage_coordOpen] at h'
    by_contra hu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {P i})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact h' (Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum A))
      (hle (Ideal.mem_span_singleton_self _))
  have e₁ := eq_spec_fromSpec (isAffineOpen_coordOpen W i) _ h'
  have e₂ := ptHom_eq_awayChart W i ρ P hP hu
  rw [← SpecMap_awayFnEquiv_awayChart, ← Category.assoc, ← Spec.map_comp] at e₁
  have e₃ := congrArg (fun φ => φ.hom (awayCoord W i j))
    (Spec.map_injective ((cancel_mono _).1 (e₁.symm.trans e₂)))
  have e₄ : evalPt _ _ h' (awayFnEquiv W i (awayCoord W i j)) =
      awayEval W i ρ P hP.equation hu (awayCoord W i j) := e₃
  rw [awayFnEquiv_awayCoord] at e₄
  rw [← awayEval_awayCoord_mul W i ρ P hP.equation hu j, ← e₄, ← evalPt_res _ hi h' h]
  rfl

end

def affineFnEquiv : W.toAffine.CoordinateRing ≃+* Γ(scheme W, coordOpen W 2) :=
  (awayEquivAffine W).symm.trans (awayFnEquiv W 2)

@[simp] theorem affineFnEquiv_affineX : affineFnEquiv W (affineX W) = ratio W 2 0 := by
  have : awayEquivAffine W (awayCoord W 2 0) = affineX W :=
    (mul_one _).symm.trans (awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one 0)
  simp [affineFnEquiv, ← this]

@[simp] theorem affineFnEquiv_affineY : affineFnEquiv W (affineY W) = ratio W 2 1 := by
  have : awayEquivAffine W (awayCoord W 2 1) = affineY W :=
    (mul_one _).symm.trans (awayEval_awayCoord_mul W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one 1)
  simp [affineFnEquiv, ← this]

@[simp] theorem affineFnEquiv_algebraMap (r : R) :
    affineFnEquiv W (algebraMap R _ r) = constOn W _ r := by
  have : awayEquivAffine W (awayConst W 2 r) = algebraMap R _ r :=
    awayEval_awayConst W 2 (algebraMap R _) ![affineX W, affineY W, 1]
      (isUnimodularSol_some (equation_affineX_affineY W)).equation isUnit_one r
  simp [affineFnEquiv, ← this]

def originFnEquiv : OriginRing W ≃+* Γ(scheme W, coordOpen W 1) :=
  (awayEquivOrigin W).symm.trans (awayFnEquiv W 1)

@[simp] theorem originFnEquiv_originZ : originFnEquiv W (originZ W) = -ratio W 1 0 := by
  have : awayEquivOrigin W (-awayCoord W 1 0) = originZ W :=
    ((map_neg _ _).trans (mul_neg_one _).symm).trans (awayEval_awayCoord_mul W 1 (algebraMap R _)
      ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg 0)
  simp [originFnEquiv, ← this]

@[simp] theorem originFnEquiv_originW : originFnEquiv W (originW W) = -ratio W 1 2 := by
  have : awayEquivOrigin W (-awayCoord W 1 2) = originW W :=
    ((map_neg _ _).trans (mul_neg_one _).symm).trans (awayEval_awayCoord_mul W 1 (algebraMap R _)
      ![originZ W, -1, originW W] (equation_originZ_originW W) isUnit_one.neg 2)
  simp [originFnEquiv, ← this]

@[simp] theorem originFnEquiv_algebraMap (r : R) :
    originFnEquiv W (algebraMap R _ r) = constOn W _ r := by
  have : awayEquivOrigin W (awayConst W 1 r) = algebraMap R _ r :=
    awayEval_awayConst W 1 (algebraMap R _) ![originZ W, -1, originW W]
      (equation_originZ_originW W) isUnit_one.neg r
  simp [originFnEquiv, ← this]

theorem originW_mem_nonZeroDivisors : originW W ∈ nonZeroDivisors (OriginRing W) := by
  have h : IsSMulRegular (OriginRing W) (Polynomial.X : Polynomial R) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (Polynomial.monic_X (R := R)).mem_nonZeroDivisors
  refine mem_nonZeroDivisors_iff_left.2 fun a ha => h ?_
  have e : algebraMap (Polynomial R) (OriginRing W) Polynomial.X = originW W :=
    AdjoinRoot.algebraMap_eq (originPolynomial W) ▸ rfl
  simp only [Algebra.smul_def, e, ha, mul_zero]

theorem isRegularFn_ratio_one_two : Cartier.IsRegularFn (ratio W 1 2) := by
  rw [Cartier.isRegularFn_iff_of_isAffineOpen (isAffineOpen_coordOpen W 1)]
  refine mem_nonZeroDivisors_iff_left.2 fun a ha => ?_
  obtain ⟨a, rfl⟩ := (originFnEquiv W).surjective a
  have : originW W * a = 0 := (originFnEquiv W).injective (by
    rw [map_mul, originFnEquiv_originW, neg_mul, ha, neg_zero, map_zero])
  rw [mem_nonZeroDivisors_iff_left.1 (originW_mem_nonZeroDivisors W) a this, map_zero]

section BaseChange

variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')

theorem mapHom_app_ratioOn {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (j : Fin 3) :
    ((mapHom W f h).app U).hom (ratioOn W U i hi j) = ratioOn W' (mapHom W f h ⁻¹ᵁ U) i
      (((mapHom W f h).preimage_mono hi).trans (mapHom_preimage_coordOpen W f h i).le) j :=
  (map_app_frac (gradedMap W f h) (irrelevant_le_map_gradedMap W f h) U _ _ _ _ hi).trans
    (frac_eq (congrArg₂ (· * ·) (homRingMap_coord W f h j) (homRingMap_coord W f h i).symm))

theorem mapHom_app_constOn (U : (scheme W).Opens) (r : R) :
    ((mapHom W f h).app U).hom (constOn W U r) = constOn W' (mapHom W f h ⁻¹ᵁ U) (f r) := by
  refine (app_baseRingHom (mapHom W f h) (toSpec W) U r).trans ?_
  rw [mapHom_toSpec, baseRingHom_comp_SpecMap]
  rfl

end BaseChange

example (hP : IsUnimodularSol ((⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℚ).map (RingHom.id ℚ)) ![2, -5, 8])
    (h : ⊤ ≤ ptHom _ _ _ hP ⁻¹ᵁ coordOpen _ 2) :
    evalPt (ptHom _ _ _ hP) _ h (ratio _ 2 0) = 1 / 4 := by
  have := evalPt_ptHom_ratioOn_mul _ _ hP le_rfl h 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val] at this
  linarith

end WeierstrassCurve

end GlobalTheory
