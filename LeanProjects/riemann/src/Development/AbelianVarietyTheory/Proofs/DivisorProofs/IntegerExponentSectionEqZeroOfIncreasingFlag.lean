import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

noncomputable section

namespace GlobalTheory.IncrZero

open Formalism.L2.Pj LaurentPolynomial

section TestRings

variable {K : Type} [Field K]

theorem isReduced_tring (p : TRing K) : IsReduced p.R :=
  (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

theorem exists_tring_inj {S : Type} [CommRing S] [IsReduced S] [Algebra K S] (p : TRing K) (ψ : p.R →ₐ[K] S)
    {J : Type} [Fintype J] (g : J → S) :
    ∃ (r : TRing K) (χ : r.R →ₐ[K] S), Function.Injective χ ∧ (∀ a, ψ a ∈ χ.range) ∧ ∀ j, g j ∈ χ.range := by
  classical
  let e := Fintype.equivFin J
  let v : Fin (p.n + Fintype.card J) → S :=
    Fin.append (fun i => ψ (Ideal.Quotient.mk p.I (MvPolynomial.X i))) (fun k => g (e.symm k))
  let Φ : MvPolynomial (Fin (p.n + Fintype.card J)) K →ₐ[K] S := MvPolynomial.aeval v
  have hrad : (RingHom.ker Φ).IsRadical := by
    intro a ⟨n, hn⟩
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.2 (IsReduced.eq_zero _ ⟨n, hn⟩)
  let r : TRing K := ⟨p.n + Fintype.card J, RingHom.ker Φ, hrad⟩
  refine ⟨r, Ideal.kerLiftAlg Φ, Ideal.kerLiftAlg_injective Φ, fun a => ?_, fun j => ?_⟩
  · obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hΦ : Φ.comp (MvPolynomial.rename (Fin.castAdd (Fintype.card J))) =
        ψ.comp (Ideal.Quotient.mkₐ K p.I) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [Φ, v, Fin.append_left]
    exact ⟨Ideal.Quotient.mk _ (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) P),
      congrArg (fun F => F P) hΦ⟩
  · exact ⟨Ideal.Quotient.mk _ (MvPolynomial.X (Fin.natAdd p.n (e j))), by
      show Φ _ = _
      simp [Φ, v, Fin.append_right]⟩

theorem exists_lift {S A B : Type} [CommRing S] [Algebra K S] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (χ : B →ₐ[K] S) (hχ : Function.Injective χ) (φ : A →ₐ[K] S) (h : ∀ a, φ a ∈ χ.range) :
    ∃ k : A →ₐ[K] B, ∀ a, χ (k a) = φ a := by
  refine ⟨(AlgEquiv.ofInjective χ hχ).symm.toAlgHom.comp (φ.codRestrict χ.range h), fun a => ?_⟩
  have e := AlgEquiv.ofInjective_apply χ hχ ((AlgEquiv.ofInjective χ hχ).symm (φ.codRestrict χ.range h a))
  rw [AlgEquiv.apply_symm_apply] at e
  exact e.symm

theorem poly_mem {R L : Type} [CommRing R] [CommRing L] [Algebra K L] (ψ : Polynomial R →+* L) (Sb : Subalgebra K L)
    (hC : ∀ a, ψ (Polynomial.C a) ∈ Sb) (hX : ψ Polynomial.X ∈ Sb) (P : Polynomial R) : ψ P ∈ Sb := by
  refine Polynomial.induction_on P hC (fun p q hp hq => ?_) (fun n a h => ?_)
  · rw [map_add]; exact add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul]; exact mul_mem h hX

end TestRings

section Laurent

variable {R : Type} [CommRing R]

theorem isReduced_poly [IsReduced R] : IsReduced (Polynomial R) :=
  ⟨fun P hP => Polynomial.ext fun i => by
    rw [Polynomial.coeff_zero]
    exact IsReduced.eq_zero _ (Polynomial.isNilpotent_iff.1 hP i)⟩

theorem isReduced_laurent [IsReduced R] : IsReduced (LaurentPolynomial R) := by
  haveI := isReduced_poly (R := R)
  refine ⟨fun q ⟨k, hk⟩ => ?_⟩
  obtain ⟨n, f, hf⟩ := exists_T_pow q
  have h1 : Polynomial.toLaurent (f ^ k) = 0 := by rw [map_pow, hf, mul_pow, hk, zero_mul]
  rw [Polynomial.toLaurent_eq_zero] at h1
  have h2 : f = 0 := IsReduced.eq_zero _ ⟨k, h1⟩
  rw [h2, map_zero] at hf
  have h3 : q = q * T (n : ℤ) * T (-(n : ℤ)) := by rw [mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
  rw [h3, ← hf, zero_mul]

theorem trunc_T_mul_aeval (m : ℤ) (hm : 0 < m) (P : Polynomial R) :
    trunc (T (-m) * Polynomial.aeval (T (-1) : LaurentPolynomial R) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, map_add, hp, hq, add_zero]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, T_pow, ← C_eq_algebraMap, mul_left_comm, ← T_add, trunc_C_mul_T]
    rw [if_neg (by push_cast; omega)]

theorem unit_zpow_eq_laurent_T_of_eq_T_one (V : (LaurentPolynomial R)ˣ) (hV : (V : LaurentPolynomial R) = T 1) (n : ℤ) :
    ((V ^ n : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = T n := by
  have hinv : ((V⁻¹ : (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = T (-1) := by
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hV, ← T_add]; simp [T_zero])
  induction n using Int.induction_on with
  | zero => simp [T_zero]
  | succ n ih => rw [zpow_add_one, Units.val_mul, ih, hV, ← T_add]
  | pred n ih => rw [zpow_sub_one, Units.val_mul, ih, hinv, ← T_add]; rfl

end Laurent

section Mat

variable {S : Type} [CommRing S] {n : ℕ} (i j : Fin n)

def uniM (x : S) : Matrix (Fin n) (Fin n) S := 1 + Matrix.single i j x

def swpM (w : S) : Matrix (Fin n) (Fin n) S :=
  1 + Matrix.single i i (w - 1) + Matrix.single i j 1 + Matrix.single j i 1 - Matrix.single j j 1

def swpInv (w : S) : Matrix (Fin n) (Fin n) S :=
  1 - Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j (-w - 1)

def triM (x ξ : S) : Matrix (Fin n) (Fin n) S :=
  1 + Matrix.single i i (x - 1) + Matrix.single j i 1 + Matrix.single j j (-ξ - 1)

variable {i j}

theorem swpM_mul_swpInv (hij : i ≠ j) (w : S) : swpM i j w * swpInv i j w = 1 := by
  ext k l
  simp only [swpM, swpInv, add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.zero_apply]
  split_ifs <;> first | ring1 | (exfalso; omega) | skip
  all_goals first | (simp_all; done) | (simp_all; ring1)

theorem triM_mul_swpM (hij : i ≠ j) (x ξ : S) (h : x * ξ = 1) : triM i j x ξ * swpM i j ξ = uniM i j x := by
  ext k l
  simp only [swpM, triM, uniM, add_mul, mul_add, sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply, Matrix.zero_apply]
  split_ifs <;> first | ring1 | (exfalso; omega) | skip
  all_goals first | (simp_all; done) | (simp_all; ring1)

theorem uniM_mul_neg (hij : i ≠ j) (x : S) : uniM i j x * uniM i j (-x) = 1 := by
  simp only [uniM, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  rw [add_assoc, ← Matrix.single_add, add_neg_cancel, Matrix.single_zero, add_zero]

theorem uniM_zero : uniM i j (0 : S) = 1 := by simp [uniM]

theorem uniM_map {K T : Type} [CommSemiring K] [CommRing T] [Algebra K S] [Algebra K T] (φ : S →ₐ[K] T) (x : S) :
    (uniM i j x).map φ = uniM i j (φ x) := by
  ext k l
  simp only [uniM, Matrix.map_apply, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem swpM_map {K T : Type} [CommSemiring K] [CommRing T] [Algebra K S] [Algebra K T] (φ : S →ₐ[K] T) (w : S) :
    (swpM i j w).map φ = swpM i j (φ w) := by
  ext k l
  simp only [swpM, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem triM_lower (hij : i < j) (x ξ : S) (k l : Fin n) (hkl : k < l) : triM i j x ξ k l = 0 := by
  simp only [triM, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> first | (exfalso; omega) | simp_all

theorem triM_diag (hij : i ≠ j) (x ξ : S) (k : Fin n) :
    triM i j x ξ k k = if k = i then x else if k = j then -ξ else 1 := by
  by_cases h1 : k = i
  · subst h1
    simp [triM, Matrix.single_apply, hij, Ne.symm hij]
  · by_cases h2 : k = j
    · subst h2
      simp [triM, Matrix.single_apply, h1, Ne.symm h1]
    · simp [triM, Matrix.single_apply, h1, h2, Ne.symm h1, Ne.symm h2]

end Mat

open Classical
open AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.FlagTan GlobalTheory.AllWt LaurentPolynomial

section Upd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def upd {S : Type} [CommRing S] (τ : E →+* ℂ) (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) :
    ∀ τ' : E →+* ℂ, Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) S :=
  Function.update (fun τ' => (1 : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) S)) τ M

variable {S : Type} [CommRing S]

theorem upd_map {K T : Type} [CommSemiring K] [CommRing T] [Algebra K S] [Algebra K T] (φ : S →ₐ[K] T)
    (τ : E →+* ℂ) (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) :
    (fun τ' => (upd τ M τ').map φ) = upd τ (M.map φ) := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp only [upd, Function.update_self]
  · simp only [upd, Function.update_of_ne h]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)

theorem upd_mul (τ : E →+* ℂ) (M N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) :
    (fun τ' => upd τ M τ' * upd τ N τ') = upd τ (M * N) := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp only [upd, Function.update_self]
  · simp only [upd, Function.update_of_ne h, Matrix.mul_one]

theorem upd_one (τ : E →+* ℂ) : upd τ (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) = fun _ => 1 := by
  funext τ'
  by_cases h : τ' = τ
  · subst h; simp only [upd, Function.update_self]
  · simp only [upd, Function.update_of_ne h]

theorem upd_det (τ : E →+* ℂ) {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} (hM : IsUnit M.det) :
    ∀ τ', IsUnit (upd τ M τ').det := fun τ' => by
  by_cases h : τ' = τ
  · subst h; simpa only [upd, Function.update_self] using hM
  · simp only [upd, Function.update_of_ne h, Matrix.det_one, isUnit_one]

end Upd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

set_option maxHeartbeats 2000000 in

theorem eq_zero_of_lt (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (τ : E →+* ℂ) (i j : Fin (Dw.mult τ))
    (hij : i < j) (he : e (some ⟨τ, i⟩) < e (some ⟨τ, j⟩)) (f : Rul Xo c) (hf : f ∈ secZ Xo c e) : f = 0 := by
  funext p y0
  show f p y0 = 0
  have hne : i ≠ j := hij.ne
  haveI := isReduced_tring p
  haveI : IsReduced (Polynomial p.R) := isReduced_poly
  haveI : IsReduced (LaurentPolynomial p.R) := isReduced_laurent

  obtain ⟨r1, χ1, hχ1, hC1, hX1⟩ :=
    exists_tring_inj p (IsScalarTower.toAlgHom c.F p.R (Polynomial p.R)) (fun _ : Unit => Polynomial.X)
  obtain ⟨α1, hα1⟩ := exists_lift χ1 hχ1 _ hC1
  obtain ⟨x1, hx1⟩ := hX1 ()
  replace hx1 : χ1 x1 = Polynomial.X := hx1
  let ev0 : r1.R →ₐ[c.F] p.R := ((Polynomial.aeval (0 : p.R)).restrictScalars c.F).comp χ1
  have hev0 : ∀ a, ev0 (α1 a) = a := fun a => by simp [ev0, hα1]
  have hevx : ev0 x1 = 0 := by simp [ev0, hx1]
  obtain ⟨y1, hy1⟩ := exists_frMap α1 y0
  obtain ⟨yX, hyX⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c r1.R (upd τ (uniM i j x1)) 1 y1).1
    (upd_det τ (Matrix.isUnit_det_of_right_inverse (uniM_mul_neg hne x1))) isUnit_one

  have h0 : f p y0 = ev0 (f r1 yX) := by
    have hb : FrMap ev0 y1 y0 := frMap_of_comp hy1 (frMap_id y0) hev0
    obtain ⟨z, hz⟩ := exists_frMap ev0 yX
    have hc := (frMap_iff_frChg hyX hb).1 hz
    rw [upd_map, uniM_map, hevx, uniM_zero, map_one, upd_one] at hc
    have hzy : z = y0 := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c p.R (fun _ => 1) 1 y0).2.1 z y0 hc
      ((frChg_calculus E H Dw l Xo c p.R).2.1 y0)
    rw [← hzy]
    exact hf.1 r1 p ev0 yX z hz

  obtain ⟨r2, χ2, hχ2, hC2, hT2⟩ := exists_tring_inj p (IsScalarTower.toAlgHom c.F p.R (LaurentPolynomial p.R))
    ![(T 1 : LaurentPolynomial p.R), T (-1)]
  have hCr : ∀ a : p.R, LaurentPolynomial.C a ∈ χ2.range := fun a => by
    rw [C_eq_algebraMap]; exact hC2 a
  obtain ⟨α2, hα2⟩ := exists_lift χ2 hχ2 ((Polynomial.toLaurentAlg.restrictScalars c.F).comp χ1) (fun a => by
    have := poly_mem (Polynomial.toLaurent) χ2.range (fun b => by rw [Polynomial.toLaurent_C]; exact hCr b)
      (by rw [Polynomial.toLaurent_X]; exact hT2 0) (χ1 a)
    simpa [Polynomial.toLaurentAlg_apply] using this)
  obtain ⟨β, hβ⟩ := exists_lift χ2 hχ2
    (((Polynomial.aeval (T (-1) : LaurentPolynomial p.R)).restrictScalars c.F).comp χ1) (fun a => by
    have := poly_mem (Polynomial.aeval (T (-1) : LaurentPolynomial p.R)).toRingHom χ2.range
      (fun b => by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]; exact hC2 b)
      (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X]; exact hT2 1) (χ1 a)
    simpa using this)
  replace hα2 : ∀ a, χ2 (α2 a) = Polynomial.toLaurent (χ1 a) := fun a => by
    rw [hα2]; simp [Polynomial.toLaurentAlg_apply]
  replace hβ : ∀ a, χ2 (β a) = Polynomial.aeval (T (-1) : LaurentPolynomial p.R) (χ1 a) := fun a => by
    rw [hβ]; simp
  set x2 := α2 x1 with hx2d
  set ξ2 := β x1 with hξ2d
  have hx2 : χ2 x2 = T 1 := by rw [hx2d, hα2, hx1, Polynomial.toLaurent_X]
  have hξ2 : χ2 ξ2 = T (-1) := by rw [hξ2d, hβ, hx1, Polynomial.aeval_X]
  have hxξ : x2 * ξ2 = 1 := hχ2 (by rw [map_mul, hx2, hξ2, ← T_add, map_one]; simp [T_zero])
  let ux : (r2.R)ˣ := ⟨x2, ξ2, hxξ, by rw [mul_comm]; exact hxξ⟩

  obtain ⟨y2, hy2⟩ := exists_frMap α2 y1
  have hy2' : FrMap (α2.comp α1) y0 y2 := frMap_comp hy1 hy2 fun _ => rfl
  have hyβ : FrMap β y1 y2 := frMap_of_comp hy1 hy2' fun a => hχ2 (by
    rw [AlgHom.comp_apply, hβ, hα2, hα1, IsScalarTower.coe_toAlgHom', Polynomial.algebraMap_eq, Polynomial.aeval_C,
      Polynomial.toLaurent_C, C_eq_algebraMap])
  obtain ⟨yX2, hyX2⟩ := exists_frMap α2 yX
  have hc2 := (frMap_iff_frChg hyX hy2).1 hyX2
  rw [upd_map, uniM_map, map_one] at hc2
  obtain ⟨yW, hyW⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c r1.R (upd τ (swpM i j x1)) 1 y1).1
    (upd_det τ (Matrix.isUnit_det_of_right_inverse (swpM_mul_swpInv hne x1))) isUnit_one
  obtain ⟨yw, hyw⟩ := exists_frMap β yW
  have hcw := (frMap_iff_frChg hyW hyβ).1 hyw
  rw [upd_map, swpM_map, map_one] at hcw
  have hct : FrChg (upd τ (triM i j x2 ξ2)) 1 yw yX2 := by
    refine ((frChg_calculus E H Dw l Xo c r2.R).1 _ _ _ _ y2 yw yX2 hcw).2 ?_
    rw [upd_mul, triM_mul_swpM hne _ _ hxξ, one_mul]
    exact hc2

  let t : Ix Dw → (r2.R)ˣ := fun k =>
    if k = some ⟨τ, i⟩ then ux else if k = some ⟨τ, j⟩ then -ux⁻¹ else 1
  have hbor : FrBor t yw yX2 := by
    refine (frBor_iff_frChg yw yX2 t).2 ⟨upd τ (triM i j x2 ξ2), fun τ' k l hkl => ?_, fun τ' k => ?_, ?_⟩
    · by_cases h : τ' = τ
      · subst h; simp only [upd, Function.update_self]; exact triM_lower hij _ _ k l hkl
      · simp only [upd, Function.update_of_ne h]; exact Matrix.one_apply_ne hkl.ne
    · by_cases h : τ' = τ
      · subst h
        simp only [upd, Function.update_self, triM_diag hne, t, Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq,
          true_and]
        split_ifs <;> simp [ux]
      · simp only [upd, Function.update_of_ne h, t, Option.some.injEq, Sigma.mk.inj_iff, h, false_and, if_false,
          Units.val_one, Matrix.one_apply_eq]
    · have : ((t none : (r2.R)ˣ) : r2.R) = 1 := by simp [t]
      rw [this]; exact hct
  have hw := hf.2 r2 t yw yX2 hbor
  have hprod : (∏ k, t k ^ e k) = ux ^ e (some ⟨τ, i⟩) * (-ux⁻¹) ^ e (some ⟨τ, j⟩) := by
    have hab : (some ⟨τ, i⟩ : Ix Dw) ≠ some ⟨τ, j⟩ := by simp [hne]
    rw [Fintype.prod_eq_mul _ _ hab (fun k hk => by simp [t, hk.1, hk.2])]
    simp [t, hab.symm]
  have hpow : ∀ n : ℤ, χ2 ((ux ^ n : (r2.R)ˣ) : r2.R) = T n := fun n => by
    have h1 : χ2 ((ux ^ n : (r2.R)ˣ) : r2.R) =
        ((Units.map (χ2 : r2.R →* LaurentPolynomial p.R) ux ^ n : (LaurentPolynomial p.R)ˣ) : LaurentPolynomial p.R) := by
      rw [← map_zpow, Units.coe_map]; simp
    rw [h1]
    exact unit_zpow_eq_laurent_T_of_eq_T_one _ (by rw [Units.coe_map]; simpa using hx2) n
  have hX2v : f r2 yX2 = α2 (f r1 yX) := hf.1 r1 r2 α2 yX yX2 hyX2
  have hwv : f r2 yw = β (f r1 yW) := hf.1 r1 r2 β yW yw hyw
  have hm : 0 < e (some ⟨τ, j⟩) - e (some ⟨τ, i⟩) := by omega
  have hψ : χ1 (f r1 yX) = 0 := by
    rw [← Polynomial.trunc_toLaurent (χ1 (f r1 yX)), ← hα2, ← hX2v, hw, hprod, hwv, map_mul, hβ]
    rcases Int.even_or_odd (e (some ⟨τ, j⟩)) with hb | hb
    · rw [Even.neg_zpow hb, inv_zpow', ← zpow_add, ← sub_eq_add_neg, hpow, ← neg_sub]
      exact trunc_T_mul_aeval _ hm _
    · rw [Odd.neg_zpow hb, mul_neg, Units.val_neg, map_neg, neg_mul, map_neg, inv_zpow', ← zpow_add,
        ← sub_eq_add_neg, hpow, ← neg_sub, trunc_T_mul_aeval _ hm, neg_zero]
  have hzero : f r1 yX = 0 := hχ1 (by rw [hψ, map_zero])
  rw [h0, hzero, map_zero]

theorem secZ_eq_zero_of_lt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ) (τ : E →+* ℂ)
    (i j : Fin (Dw.mult τ)), i < j → e (some ⟨τ, i⟩) < e (some ⟨τ, j⟩) → ∀ f ∈ secZ Xo c e, f = 0 :=
  fun _ _ _ _ _ _ _ Xo c e τ i j hij he f hf => eq_zero_of_lt Xo c e τ i j hij he f hf

end GlobalTheory.IncrZero
