import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

namespace OneLetterPf

section HS

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hs_add_l (A A' C : Wq →L[ℂ] Wp) : B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, inner_add_right,
    Finset.sum_add_distrib]

theorem hs_add_r (A C C' : Wq →L[ℂ] Wp) : B.hsInner A (C + C') = B.hsInner A C + B.hsInner A C' := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, inner_add_left,
    Finset.sum_add_distrib]

theorem hs_smul_l (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_smul_right,
    Finset.mul_sum]

theorem hs_smul_r (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_smul_left,
    Finset.mul_sum]

theorem hs_neg_l (A C : Wq →L[ℂ] Wp) : B.hsInner (-A) C = -B.hsInner A C := by
  rw [← neg_one_smul ℂ A, hs_smul_l]; ring

theorem hs_neg_r (A C : Wq →L[ℂ] Wp) : B.hsInner A (-C) = -B.hsInner A C := by
  rw [← neg_one_smul ℂ C, hs_smul_r]; simp

theorem hs_zero_l (C : Wq →L[ℂ] Wp) : B.hsInner 0 C = 0 := by
  rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hs_smul_l]; ring

theorem hs_zero_r (A : Wq →L[ℂ] Wp) : B.hsInner A 0 = 0 := by
  rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hs_smul_r]; simp

theorem plus_pt (t Y : ℂ) (ht : t ≠ 0) (hY : conj Y = Y) (A0 A1 B0 B1 SubquotientNontrivial ProjectiveBundleFormulaTorsion : Wq →L[ℂ] Wp) :
    B.hsInner (-((conj t)⁻¹ • A1)) (Y • B0 + ProjectiveBundleFormulaTorsion - t • B1) +
      B.hsInner (conj t • A0 + (Y + 1) • A1 - SubquotientNontrivial) (t⁻¹ • B0) =
    (B.hsInner A0 B0 + B.hsInner A1 B1) + (conj t)⁻¹ * B.hsInner A1 B0 -
      B.hsInner ((conj t)⁻¹ • SubquotientNontrivial) B0 - B.hsInner A1 (t⁻¹ • ProjectiveBundleFormulaTorsion) := by
  have hct : conj t ≠ 0 := (map_ne_zero _).mpr ht
  simp only [sub_eq_add_neg, hs_add_l, hs_add_r, hs_smul_l, hs_smul_r, hs_neg_l, hs_neg_r, map_inv₀, hY,
    Complex.conj_conj]
  field_simp
  ring

theorem minus_pt (t Y : ℂ) (ht : t ≠ 0) (hY : conj Y = Y) (A0 A1 B0 B1 SubquotientNontrivial ProjectiveBundleFormulaTorsion : Wq →L[ℂ] Wp) :
    B.hsInner (-(t⁻¹ • A1)) (Y • B0 - ProjectiveBundleFormulaTorsion - conj t • B1) +
      B.hsInner (t • A0 + (Y - 1) • A1 + SubquotientNontrivial) ((conj t)⁻¹ • B0) =
    (B.hsInner A0 B0 + B.hsInner A1 B1) - t⁻¹ * B.hsInner A1 B0 +
      B.hsInner (t⁻¹ • SubquotientNontrivial) B0 + B.hsInner A1 ((conj t)⁻¹ • ProjectiveBundleFormulaTorsion) := by
  have hct : conj t ≠ 0 := (map_ne_zero _).mpr ht
  simp only [sub_eq_add_neg, hs_add_l, hs_add_r, hs_smul_l, hs_smul_r, hs_neg_l, hs_neg_r, map_inv₀, hY,
    Complex.conj_conj]
  field_simp
  ring

end HS

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem pfst_zero : (0 : Pr V).1 = 0 := rfl
theorem pfst_one : (1 : Pr V).1 = 1 := rfl
theorem pfst_add (x y : Pr V) : (x + y).1 = x.1 + y.1 := rfl
theorem pfst_neg (x : Pr V) : (-x).1 = -x.1 := rfl
theorem pfst_sub (x y : Pr V) : (x - y).1 = x.1 - y.1 := rfl
theorem pfst_one_apply (Φ : V) : (1 : Pr V).1 Φ = Φ := rfl
theorem pfst_alg (Y : ℂ) (Φ : V) : (algebraMap ℂ (Pr V) Y).1 Φ = Y • Φ := rfl
theorem pfst_star_alg (Y : ℂ) (Φ : V) : (star (algebraMap ℂ (Pr V) Y)).1 Φ = conj Y • Φ := rfl
theorem pfst_mkP (X Xs : Module.End ℂ V) : (mkP X Xs : Pr V).1 = X := rfl
theorem pfst_star_mkP (X Xs : Module.End ℂ V) : (star (mkP X Xs : Pr V)).1 = Xs := rfl

theorem ins_apply1 (a : S) (M : M2 (Pr V)) (y y' : Ix S) :
    (ins a (lift0 M) : SlopeTestRemainingChoices S (Pr V)) y y' = ∑ j, if y' = Function.update y a j then M (y a) j else 0 := by
  unfold ins lift0
  simp only [Matrix.sum_apply, Matrix.map_apply]
  have hm : ∀ i j, (((eU a i j : SlopeTestRemainingChoices S (Pr V)) * (io (M i j) : SlopeTestRemainingChoices S (Pr V)) : SlopeTestRemainingChoices S (Pr V))) y y' =
      if y a = i ∧ y' = Function.update y a j then M i j else 0 := by
    intro i j
    simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Formalism.FourierDecayAlt.P.Wd1.eU_apply, ite_mul, one_mul, zero_mul]
  simp only [hm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (y a)]
  · simp
  · intro i _ hi; simp [Ne.symm hi]
  · simp

end Act

section ActR

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem action_inserted_letter_apply (a : S) (M : M2 (Pr (RadSp k r z z' π π'))) (u : Ix S → RadSp k r z z' π π') (y : Ix S) :
    act (ins a (lift0 M)) u y = ∑ j, (M (y a) j).1 (u (Function.update y a j)) := by
  simp only [act, ins_apply1, pr_fst_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (Function.update y a j)]
  · simp
  · intro b _ hb; simp [hb, pfst_zero]
  · simp

theorem action_elementary_unit_apply (a : S) (i j : Fin 2) (u : Ix S → RadSp k r z z' π π') (y : Ix S) :
    act (eU a i j : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) u y = if y a = i then u (Function.update y a j) else 0 := by
  simp only [act, Formalism.FourierDecayAlt.P.Wd1.eU_apply]
  rw [Finset.sum_eq_single (Function.update y a j)]
  · by_cases h : y a = i <;> simp [h, pfst_one, pfst_zero]
  · intro b _ hb; simp [hb, pfst_zero]
  · simp

theorem fin_two_eq_one_of_ne_zero {q : Fin 2} (h : q ≠ 0) : q = 1 := by
  fin_cases q <;> simp_all

theorem sum_split (a : S) {M : Type} [AddCommMonoid M] (f : Ix S → M) :
    ∑ y, f y = ∑ y, if y a = 0 then f y + f (Function.update y a 1) else 0 := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_add_distrib,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : Ix S => y a = 0) f]
  congr 1
  refine Finset.sum_nbij' (fun y => Function.update y a 0) (fun y => Function.update y a 1) ?_ ?_ ?_ ?_ ?_
  · intro y _; simp
  · intro y _; simp
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have h1 := fin_two_eq_one_of_ne_zero hy
    funext b
    by_cases hb : b = a
    · subst hb; simp [h1]
    · simp [Function.update_of_ne hb]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    funext b
    by_cases hb : b = a
    · subst hb; simp [hy]
    · simp [Function.update_of_ne hb]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have h1 := fin_two_eq_one_of_ne_zero hy
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb; simp [h1]
    · simp [Function.update_of_ne hb]

end ActR

section Cls

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem opv1 (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (h : Mx k r) :
    ((X.op l 1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p h = p l • (Φ : Fn k r (Wq →L[ℂ] Wp)) p h := by
  rw [X.op_apply]; rfl

theorem opv2 (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (h : Mx k r) :
    ((X.op l 2 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p h = (p l)⁻¹ • (Φ : Fn k r (Wq →L[ℂ] Wp)) p h := by
  rw [X.op_apply]; rfl

theorem opv4 (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (h : Mx k r) :
    ((X.op l 4 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p h = conj (p l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) p h := by
  rw [X.op_apply]; rfl

theorem opv5 (X : ActualOps k r z z' π π') (l : Fin r) (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (h : Mx k r) :
    ((X.op l 5 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) p h =
      (conj (p l))⁻¹ • (Φ : Fn k r (Wq →L[ℂ] Wp)) p h := by
  rw [X.op_apply]; rfl

theorem opClos_op (X : ActualOps k r z z' π π') (l : Fin r) (Bs : Submodule ℂ (RadSp k r z z' π π')) (j : Fin 6)
    {Φ : RadSp k r z z' π π'} (h : Φ ∈ OpClos X l Bs) : X.op l j Φ ∈ OpClos X l Bs := by
  unfold OpClos at h ⊢
  refine (Submodule.span_le.mpr ?_ : _ ≤ (Submodule.span ℂ _).comap (X.op l j)) h
  rintro _ ⟨js, Ψ, hΨ, rfl⟩
  exact Submodule.subset_span ⟨j :: js, Ψ, hΨ, by simp [List.map_cons, List.prod_cons, Module.End.mul_apply]⟩

theorem opClos_lc (X : ActualOps k r z z' π π') (l : Fin r) (Bs : Submodule ℂ (RadSp k r z z' π π'))
    (hB : Bs ≤ lcSub k r z z' π π') : OpClos X l Bs ≤ lcSub k r z z' π π' := by
  unfold OpClos
  rw [Submodule.span_le]
  rintro _ ⟨js, Ψ, hΨ, rfl⟩
  induction js with
  | nil => simpa using hB hΨ
  | cons j js ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    exact op_lc X l j _ ih

end Cls

section ClsP

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem clsE_lc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) :
    ClsE S P z z' π π' X L st l0 D l ≤ lcSub P.k P.r z z' π π' := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) (D := D) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) 0
  refine opClos_lc X l _ (sup_le hle ?_)
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, a, b, Ψ, hΨ, rfl⟩
  exact (RRi_lc X μ L st l0 hD 0 w hw.1.2.1 a b).1 _ (hle hΨ)

theorem clsE_op (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r) (j : Fin 6) {Φ : RadSp P.k P.r z z' π π'}
    (h : Φ ∈ ClsE S P z z' π π' X L st l0 D l) : X.op l j Φ ∈ ClsE S P z z' π π' X L st l0 D l :=
  opClos_op X l _ j h

theorem clsE_eU (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r) (a : S) (i j : Fin 2) (v : Ix S → RadSp P.k P.r z z' π π')
    (hv : ∀ b, v b ∈ ClsE S P z z' π π' X L st l0 D l) (y : Ix S) :
    act (eU a i j : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) v y ∈ ClsE S P z z' π π' X L st l0 D l := by
  rw [action_elementary_unit_apply]
  split_ifs
  · exact hv _
  · exact zero_mem _

end ClsP

section Pt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem upd_self (y : Ix S) (a : S) (hy : y a = 0) : Function.update y a 0 = y := by
  rw [← hy]; exact Function.update_eq_self a y

theorem upd_upd (y : Ix S) (a : S) (i j : Fin 2) :
    Function.update (Function.update y a i) a j = Function.update y a j := Function.update_idem _ _ _

theorem ivlet_plus_0 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = true)
    (u : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (ivlet (site L l) le) u y = -X.op l 5 (u (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [ivlet, hp, action_inserted_letter_apply, hy, Fin.sum_univ_two, site, hAL.2.2.2.1 l, pfst_neg, pfst_zero, pfst_star_mkP]

theorem ivlet_plus_1 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = true)
    (u : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (ivlet (site L l) le) u (Function.update y le.intersection_update_fsHerm_neg_one 1) =
      X.op l 4 (u y) + (le.pt + 1) • u (Function.update y le.intersection_update_fsHerm_neg_one 1) - X.op l 3 (u (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [ivlet, hp, action_inserted_letter_apply, upd_upd, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, hAL.1 l, hAL.2.2.1 l,
    pfst_neg, pfst_zero, pfst_star_mkP, pfst_add, pfst_alg, sub_eq_add_neg, add_smul]
  abel

theorem vlet_plus_0 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = true)
    (v : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (vlet (site L l) le) v y = le.pt • v y + X.op l 0 (v y) - X.op l 1 (v (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [vlet, hp, action_inserted_letter_apply, hy, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, Ts, YangianSpanCharacter.T.Tm, hAL.1 l, hAL.2.2.1 l,
    pfst_neg, pfst_add, pfst_alg, pfst_mkP, sub_eq_add_neg]

theorem vlet_plus_1 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = true)
    (v : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (vlet (site L l) le) v (Function.update y le.intersection_update_fsHerm_neg_one 1) = X.op l 2 (v y) := by
  simp [vlet, hp, action_inserted_letter_apply, upd_upd, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, Ts, YangianSpanCharacter.T.Tm, hAL.2.2.2.1 l,
    pfst_zero, pfst_mkP]

theorem ivlet_minus_0 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = false)
    (u : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (ivlet (site L l) le) u y = -X.op l 2 (u (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [ivlet, hp, action_inserted_letter_apply, hy, Fin.sum_univ_two, site, hAL.2.2.2.1 l, pfst_neg, pfst_zero, pfst_mkP]

theorem ivlet_minus_1 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = false)
    (u : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (ivlet (site L l) le) u (Function.update y le.intersection_update_fsHerm_neg_one 1) =
      X.op l 1 (u y) + (le.pt - 1) • u (Function.update y le.intersection_update_fsHerm_neg_one 1) + X.op l 0 (u (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [ivlet, hp, action_inserted_letter_apply, upd_upd, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, hAL.1 l, hAL.2.2.1 l,
    pfst_zero, pfst_mkP, pfst_add, pfst_alg, pfst_sub, pfst_one_apply, sub_smul]
  abel

theorem vlet_minus_0 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = false)
    (v : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (vlet (site L l) le) v y =
      conj le.pt • v y - X.op l 3 (v y) - X.op l 4 (v (Function.update y le.intersection_update_fsHerm_neg_one 1)) := by
  simp [vlet, hp, action_inserted_letter_apply, hy, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, Ts, YangianSpanCharacter.T.Tm, hAL.1 l, hAL.2.2.1 l,
    pfst_neg, pfst_add, pfst_star_alg, pfst_star_mkP, sub_eq_add_neg]

theorem vlet_minus_1 (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = false)
    (v : Ix S → RadSp k r z z' π π') (y : Ix S) (hy : y le.intersection_update_fsHerm_neg_one = 0) :
    act (vlet (site L l) le) v (Function.update y le.intersection_update_fsHerm_neg_one 1) = X.op l 5 (v y) := by
  simp [vlet, hp, action_inserted_letter_apply, upd_upd, upd_self y le.intersection_update_fsHerm_neg_one hy, Fin.sum_univ_two, site, Ts, YangianSpanCharacter.T.Tm, hAL.2.2.2.1 l,
    pfst_zero, pfst_star_mkP]

end Pt

section SumPt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem sum_comb (a : S) (f g1 g2 g3 g4 : Ix S → ℂ) (c : ℂ)
    (H : ∀ y, y a = 0 → f y + f (Function.update y a 1) = (g1 y + g1 (Function.update y a 1)) +
      c * (g2 y + g2 (Function.update y a 1)) - (g3 y + g3 (Function.update y a 1)) -
      (g4 y + g4 (Function.update y a 1))) :
    ∑ y, f y = ∑ y, g1 y + c * ∑ y, g2 y - ∑ y, g3 y - ∑ y, g4 y := by
  rw [sum_split a f, sum_split a g1, sum_split a g2, sum_split a g3, sum_split a g4, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hy
  · exact H y hy
  · simp

abbrev vl (Φ : RadSp k r z z' π π') (p : Fin r → ℂ) (h : Mx k r) : Wq →L[ℂ] Wp :=
  (Φ : Fn k r (Wq →L[ℂ] Wp)) p h

theorem sumPt_plus (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = true) (hY : conj le.pt = le.pt)
    (u v : Ix S → RadSp k r z z' π π') (p : Fin r → ℂ) (ht : p l ≠ 0) (h : Mx k r) :
    ∑ y, B.hsInner (vl (act (ivlet (site L l) le) u y) p h) (vl (act (vlet (site L l) le) v y) p h) =
      ∑ y, B.hsInner (vl (u y) p h) (vl (v y) p h) +
      (conj (p l))⁻¹ * ∑ y, B.hsInner (vl (u y) p h) (vl (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y) p h) -
      ∑ y, B.hsInner (vl (X.op l 5 (X.op l 3 (u y))) p h) (vl (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y) p h) -
      ∑ y, B.hsInner (vl (u y) p h) (vl (X.op l 2 (X.op l 0 (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y))) p h) := by
  refine sum_comb le.intersection_update_fsHerm_neg_one _ _ _ _ _ _ fun y hy => ?_
  have hy1 : Function.update y le.intersection_update_fsHerm_neg_one 1 le.intersection_update_fsHerm_neg_one = 1 := by simp
  rw [ivlet_plus_0 X L hAL l le hp u y hy, ivlet_plus_1 X L hAL l le hp u y hy, vlet_plus_0 X L hAL l le hp v y hy,
    vlet_plus_1 X L hAL l le hp v y hy, action_elementary_unit_apply, action_elementary_unit_apply, if_neg (by rw [hy]; decide), if_pos hy1, upd_upd,
    upd_self y le.intersection_update_fsHerm_neg_one hy]
  have hct : conj (p l) ≠ 0 := (map_ne_zero _).mpr ht
  simp only [vl, map_zero, ZeroMemClass.coe_zero, Pi.zero_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, opv1, opv2, opv4,
    opv5, sub_eq_add_neg, hs_add_l, hs_add_r, hs_smul_l, hs_smul_r, hs_neg_l, hs_neg_r, hs_zero_l, hs_zero_r, map_inv₀,
    hY, Complex.conj_conj]
  field_simp
  ring

theorem sumPt_minus (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (hp : le.plus = false) (hY : conj le.pt = le.pt)
    (u v : Ix S → RadSp k r z z' π π') (p : Fin r → ℂ) (ht : p l ≠ 0) (h : Mx k r) :
    ∑ y, B.hsInner (vl (act (ivlet (site L l) le) u y) p h) (vl (act (vlet (site L l) le) v y) p h) =
      ∑ y, B.hsInner (vl (u y) p h) (vl (v y) p h) +
      (-(p l)⁻¹) * ∑ y, B.hsInner (vl (u y) p h) (vl (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y) p h) -
      (-∑ y, B.hsInner (vl (X.op l 2 (X.op l 0 (u y))) p h) (vl (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y) p h)) -
      (-∑ y, B.hsInner (vl (u y) p h) (vl (X.op l 5 (X.op l 3 (act (eU le.intersection_update_fsHerm_neg_one 1 0) v y))) p h)) := by
  simp only [← Finset.sum_neg_distrib]
  refine sum_comb le.intersection_update_fsHerm_neg_one _ _ _ _ _ _ fun y hy => ?_
  have hy1 : Function.update y le.intersection_update_fsHerm_neg_one 1 le.intersection_update_fsHerm_neg_one = 1 := by simp
  rw [ivlet_minus_0 X L hAL l le hp u y hy, ivlet_minus_1 X L hAL l le hp u y hy,
    vlet_minus_0 X L hAL l le hp v y hy, vlet_minus_1 X L hAL l le hp v y hy, action_elementary_unit_apply, action_elementary_unit_apply,
    if_neg (by rw [hy]; decide), if_pos hy1, upd_upd, upd_self y le.intersection_update_fsHerm_neg_one hy]
  have hct : conj (p l) ≠ 0 := (map_ne_zero _).mpr ht
  simp only [vl, map_zero, ZeroMemClass.coe_zero, Pi.zero_apply, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_neg, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, opv1, opv2, opv4,
    opv5, sub_eq_add_neg, hs_add_l, hs_add_r, hs_smul_l, hs_smul_r, hs_neg_l, hs_neg_r, hs_zero_l, hs_zero_r, map_inv₀,
    hY, Complex.conj_conj, map_neg]
  field_simp
  ring

end SumPt

section Int

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def hsSum (x y : Ix S → RadSp k r z z' π π') (p : Fin r → ℂ) (g : Mt k r) : ℂ :=
  ∑ b, B.hsInner (vl (x b) p (Matrix.of g)) (vl (y b) p (Matrix.of g))

theorem hsSum_int (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x y : Ix S → RadSp k r z z' π π')
    (hx : ∀ b, x b ∈ lcSub k r z z' π π') (hy : ∀ b, y b ∈ lcSub k r z z' π π') (p : Fin r → ℂ) :
    Integrable (hsSum x y p) μ := by
  unfold hsSum
  exact integrable_finset_sum _ fun b _ => int_lc μ hμ (hx b) (hy b) p

theorem pairSum_eq (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (x y : Ix S → RadSp k r z z' π π')
    (hx : ∀ b, x b ∈ lcSub k r z z' π π') (hy : ∀ b, y b ∈ lcSub k r z z' π π') (p : Fin r → ℂ) :
    ∑ b, pairAt μ (x b) (y b) p = ∫ g, hsSum x y p g ∂μ := by
  unfold hsSum pairAt
  rw [integral_finset_sum _ fun b _ => int_lc μ hμ (hx b) (hy b) p]

theorem int4 {α : Type} [MeasurableSpace α] {ν : Measure α} (f1 f2 f3 f4 : α → ℂ) (c d : ℂ)
    (i1 : Integrable f1 ν) (i2 : Integrable f2 ν) (i3 : Integrable f3 ν) (i4 : Integrable f4 ν) :
    ∫ a, f1 a + c * f2 a + d * f3 a + d * f4 a ∂ν = ∫ a, f1 a ∂ν + c * ∫ a, f2 a ∂ν + d * ∫ a, f3 a ∂ν +
      d * ∫ a, f4 a ∂ν := by
  rw [integral_add (f := fun a => f1 a + c * f2 a + d * f3 a) (g := fun a => d * f4 a)
      (by exact (i1.add (i2.const_mul c)).add (i3.const_mul d)) (by exact i4.const_mul d),
    integral_add (f := fun a => f1 a + c * f2 a) (g := fun a => d * f3 a)
      (by exact i1.add (i2.const_mul c)) (by exact i3.const_mul d),
    integral_add (f := fun a => f1 a) (g := fun a => c * f2 a) i1 (by exact i2.const_mul c),
    integral_const_mul, integral_const_mul, integral_const_mul]

theorem form_comb (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    (c1 : Fin r → ℂ) (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 : Ix S → RadSp k r z z' π π') (c d : ℂ)
    (h0 : ∀ b, x0 b ∈ lcSub k r z z' π π' ∧ y0 b ∈ lcSub k r z z' π π')
    (h1 : ∀ b, x1 b ∈ lcSub k r z z' π π' ∧ y1 b ∈ lcSub k r z z' π π')
    (h2 : ∀ b, x2 b ∈ lcSub k r z z' π π' ∧ y2 b ∈ lcSub k r z z' π π')
    (h3 : ∀ b, x3 b ∈ lcSub k r z z' π π' ∧ y3 b ∈ lcSub k r z z' π π')
    (h4 : ∀ b, x4 b ∈ lcSub k r z z' π π' ∧ y4 b ∈ lcSub k r z z' π π')
    (I1 : ∀ b, LevelSquareIntegrable μ i (x1 b) c1 ∧ LevelSquareIntegrable μ i (y1 b) c1) (I2 : ∀ b, LevelSquareIntegrable μ i (x2 b) c1 ∧ LevelSquareIntegrable μ i (y2 b) c1)
    (I3 : ∀ b, LevelSquareIntegrable μ i (x3 b) c1 ∧ LevelSquareIntegrable μ i (y3 b) c1) (I4 : ∀ b, LevelSquareIntegrable μ i (x4 b) c1 ∧ LevelSquareIntegrable μ i (y4 b) c1)
    (H : ∀ (c' : Cf r i) (g : Mt k r), hsSum x0 y0 (glue i c1 c') g =
      hsSum x1 y1 (glue i c1 c') g + c * hsSum x2 y2 (glue i c1 c') g + d * hsSum x3 y3 (glue i c1 c') g +
        d * hsSum x4 y4 (glue i c1 c') g) :
    form μ i x0 y0 c1 = form μ i x1 y1 c1 + c * form μ i x2 y2 c1 + d * form μ i x3 y3 c1 + d * form μ i x4 y4 c1 := by
  have hp : ∀ c' : Cf r i, ∑ b, pairAt μ (x0 b) (y0 b) (glue i c1 c') =
      ∑ b, pairAt μ (x1 b) (y1 b) (glue i c1 c') + c * ∑ b, pairAt μ (x2 b) (y2 b) (glue i c1 c') +
        d * ∑ b, pairAt μ (x3 b) (y3 b) (glue i c1 c') + d * ∑ b, pairAt μ (x4 b) (y4 b) (glue i c1 c') := by
    intro c'
    have J := fun (x y : Ix S → RadSp k r z z' π π') (h : ∀ b, x b ∈ lcSub k r z z' π π' ∧ y b ∈ lcSub k r z z' π π') =>
      hsSum_int μ hμ x y (fun b => (h b).1) (fun b => (h b).2) (glue i c1 c')
    rw [pairSum_eq μ hμ x0 y0 (fun b => (h0 b).1) (fun b => (h0 b).2),
      pairSum_eq μ hμ x1 y1 (fun b => (h1 b).1) (fun b => (h1 b).2),
      pairSum_eq μ hμ x2 y2 (fun b => (h2 b).1) (fun b => (h2 b).2),
      pairSum_eq μ hμ x3 y3 (fun b => (h3 b).1) (fun b => (h3 b).2),
      pairSum_eq μ hμ x4 y4 (fun b => (h4 b).1) (fun b => (h4 b).2),
      integral_congr_ae (Filter.Eventually.of_forall (H c'))]
    exact int4 _ _ _ _ c d (J x1 y1 h1) (J x2 y2 h2) (J x3 y3 h3) (J x4 y4 h4)
  have O := fun (x y : Ix S → RadSp k r z z' π π') (h : ∀ b, x b ∈ lcSub k r z z' π π' ∧ y b ∈ lcSub k r z z' π π')
      (I : ∀ b, LevelSquareIntegrable μ i (x b) c1 ∧ LevelSquareIntegrable μ i (y b) c1) =>
    formIntOuter_of_l2I μ hμ i x y (fun b => (h b).1) (fun b => (h b).2) c1 (fun b => (I b).1) (fun b => (I b).2)
  unfold form
  simp_rw [hp]
  have e : ∀ c' : Cf r i, ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (∑ b, pairAt μ (x1 b) (y1 b) (glue i c1 c') + c * ∑ b, pairAt μ (x2 b) (y2 b) (glue i c1 c') +
        d * ∑ b, pairAt μ (x3 b) (y3 b) (glue i c1 c') + d * ∑ b, pairAt μ (x4 b) (y4 b) (glue i c1 c')) =
      ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (x1 b) (y1 b) (glue i c1 c') +
        c * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (x2 b) (y2 b) (glue i c1 c')) +
        d * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (x3 b) (y3 b) (glue i c1 c')) +
        d * (((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, pairAt μ (x4 b) (y4 b) (glue i c1 c')) := fun c' => by ring
  simp_rw [e]
  exact int4 _ _ _ _ c d (O x1 y1 h1 I1) (O x2 y2 h2 I2) (O x3 y3 h3 I3) (O x4 y4 h4 I4)

end Int

section Wirt

theorem wirt_mul (b : Bool) {f g : ℂ → ℂ} {t : ℂ} (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    wirt b (fun s => f s * g s) t = wirt b f t * g t + f t * wirt b g t := by
  have hm : HasFDerivAt (fun s => f s * g s) (f t • fderiv ℝ g t + g t • fderiv ℝ f t) t :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  unfold wirt
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_q (t : ℂ) :
    HasFDerivAt (fun s : ℂ => s * conj s)
      (t • (Complex.conjCLE : ℂ →L[ℝ] ℂ) + conj t • ContinuousLinearMap.id ℝ ℂ) t := by
  exact (hasFDerivAt_id (𝕜 := ℝ) t).mul (Complex.conjCLE.hasFDerivAt (x := t))

theorem wirt_q (b : Bool) (t : ℂ) : wirt b (fun s : ℂ => s * conj s) t = if b then conj t else t := by
  unfold wirt
  rw [(hasFDerivAt_q t).fderiv]
  cases b <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem q_wt (s : ℂ) (hs : s ≠ 0) : s * conj s * ((‖s‖ ^ (-2 : ℤ) : ℝ) : ℂ) = 1 := by
  have hn : (‖s‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hs
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [zpow_neg, zpow_ofNat]
  field_simp

end Wirt

section LetterLc

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem split_y (a : S) (y : Ix S) : ∃ y0 : Ix S, y0 a = 0 ∧ (y = y0 ∨ y = Function.update y0 a 1) := by
  refine ⟨Function.update y a 0, by simp, ?_⟩
  by_cases h : y a = 0
  · left; rw [upd_self y a h]
  · right
    rw [upd_upd, ← fin_two_eq_one_of_ne_zero h]
    exact (Function.update_eq_self a y).symm

theorem act_letter_lc (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)
    (hAL : IsActualLevel X L) (l : Fin r) (le : Letter ℂ S) (u : Ix S → RadSp k r z z' π π')
    (hu : ∀ b, u b ∈ lcSub k r z z' π π') (y : Ix S) :
    act (ivlet (site L l) le) u y ∈ lcSub k r z z' π π' ∧ act (vlet (site L l) le) u y ∈ lcSub k r z z' π π' := by
  have hop := op_lc X l
  obtain ⟨y0, hy0, h | h⟩ := split_y le.intersection_update_fsHerm_neg_one y <;> rw [h] <;> cases hp : le.plus
  · rw [ivlet_minus_0 X L hAL l le hp u y0 hy0, vlet_minus_0 X L hAL l le hp u y0 hy0]
    exact ⟨neg_mem (hop _ _ (hu _)), sub_mem (sub_mem (Submodule.smul_mem _ _ (hu _)) (hop _ _ (hu _)))
      (hop _ _ (hu _))⟩
  · rw [ivlet_plus_0 X L hAL l le hp u y0 hy0, vlet_plus_0 X L hAL l le hp u y0 hy0]
    exact ⟨neg_mem (hop _ _ (hu _)), sub_mem (add_mem (Submodule.smul_mem _ _ (hu _)) (hop _ _ (hu _)))
      (hop _ _ (hu _))⟩
  · rw [ivlet_minus_1 X L hAL l le hp u y0 hy0, vlet_minus_1 X L hAL l le hp u y0 hy0]
    exact ⟨add_mem (add_mem (hop _ _ (hu _)) (Submodule.smul_mem _ _ (hu _))) (hop _ _ (hu _)), hop _ _ (hu _)⟩
  · rw [ivlet_plus_1 X L hAL l le hp u y0 hy0, vlet_plus_1 X L hAL l le hp u y0 hy0]
    exact ⟨sub_mem (add_mem (hop _ _ (hu _)) (Submodule.smul_mem _ _ (hu _))) (hop _ _ (hu _)), hop _ _ (hu _)⟩

end LetterLc

section Core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem glue_succ_self (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  simp [glue]

theorem eU_mem (K : Submodule ℂ (RadSp k r z z' π π')) (a : S) (i j : Fin 2) (v : Ix S → RadSp k r z z' π π')
    (hv : ∀ b, v b ∈ K) (y : Ix S) : act (eU a i j : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v y ∈ K := by
  rw [action_elementary_unit_apply]
  split_ifs
  · exact hv _
  · exact zero_mem _

theorem core (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (hAL : IsActualLevel X L)
    (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) (le : Letter ℂ S)
    (hY : conj le.pt = le.pt) (K : Submodule ℂ (RadSp k r z z' π π'))
    (hKop : ∀ (j : Fin 6) Φ, Φ ∈ K → X.op l j Φ ∈ K) (hKlc : K ≤ lcSub k r z z' π π')
    (c : Fin r → ℂ) (t : ℂ) (ht : t ≠ 0)
    (hL2 : ∀ x y : Ix S → RadSp k r z z' π π', (∀ b, x b ∈ K) → (∀ b, y b ∈ K) →
      ∀ b, LevelSquareIntegrable μ l.succ (x b) (Function.update c l t) ∧ LevelSquareIntegrable μ l.succ (y b) (Function.update c l t))
    (hDf : ∀ x y : Ix S → RadSp k r z z' π π', (∀ b, x b ∈ K) → (∀ b, y b ∈ K) →
      DifferentiableAt ℝ (Dens μ l x y c) t)
    (hLb : ∀ x y : Ix S → RadSp k r z z' π π', (∀ b, x b ∈ K) → (∀ b, y b ∈ K) →
      wirt true (fun t => form μ l.succ x y (Function.update c l t)) t =
        form μ l.succ (fun b => X.op l 2 (X.op l 0 (x b))) y (Function.update c l t) +
          form μ l.succ x (fun b => X.op l 5 (X.op l 3 (y b))) (Function.update c l t) ∧
      wirt false (fun t => form μ l.succ x y (Function.update c l t)) t =
        form μ l.succ (fun b => X.op l 5 (X.op l 3 (x b))) y (Function.update c l t) +
          form μ l.succ x (fun b => X.op l 2 (X.op l 0 (y b))) (Function.update c l t))
    (u v : Ix S → RadSp k r z z' π π') (hu : ∀ b, u b ∈ K) (hv : ∀ b, v b ∈ K) :
    Dens μ l (act (ivlet (site L l) le) u) (act (vlet (site L l) le) v) c t =
      Dens μ l u v c t + (if le.plus then (-1 : ℂ) else 1) *
        wirt (!le.plus) (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c) t := by
  have hE : ∀ b, act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v b ∈ K := eU_mem K le.intersection_update_fsHerm_neg_one 1 0 v hv
  have hop2 : ∀ (i j : Fin 6) (x : Ix S → RadSp k r z z' π π'), (∀ b, x b ∈ K) →
      ∀ b, X.op l i (X.op l j (x b)) ∈ K := fun i j x hx b => hKop i _ (hKop j _ (hx b))
  have LC : ∀ x y : Ix S → RadSp k r z z' π π', (∀ b, x b ∈ K) → (∀ b, y b ∈ K) →
      ∀ b, x b ∈ lcSub k r z z' π π' ∧ y b ∈ lcSub k r z z' π π' := fun x y hx hy b => ⟨hKlc (hx b), hKlc (hy b)⟩
  have h0 : ∀ b, act (ivlet (site L l) le) u b ∈ lcSub k r z z' π π' ∧
      act (vlet (site L l) le) v b ∈ lcSub k r z z' π π' := fun b =>
    ⟨(act_letter_lc X L hAL l le u (fun b => hKlc (hu b)) b).1, (act_letter_lc X L hAL l le v (fun b => hKlc (hv b)) b).2⟩
  have hq := q_wt t ht
  have hev : (fun s => form μ l.succ u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (Function.update c l s)) =ᶠ[𝓝 t]
      (fun s => s * conj s * Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c s) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds ht] with s hs
    simp only [Dens]
    rw [← mul_assoc, q_wt s hs, one_mul]
  have hprod : ∀ bb : Bool, wirt bb (fun s => form μ l.succ u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (Function.update c l s)) t = (if bb then conj t else t) * Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0) v) c t +
        t * conj t * wirt bb (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c) t := by
    intro bb
    have e1 : wirt bb (fun s => form μ l.succ u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
        (Function.update c l s)) t =
        wirt bb (fun s => s * conj s * Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c s) t := by
      unfold wirt; rw [hev.fderiv_eq]
    have e2 := wirt_mul bb (f := fun s : ℂ => s * conj s)
      (g := Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c)
      (hasFDerivAt_q t).differentiableAt (hDf u _ hu hE)
    beta_reduce at e2
    rw [e1, e2, wirt_q]
  cases hp : le.plus
  ·
    have hform := form_comb μ hμ l.succ (Function.update c l t) (act (ivlet (site L l) le) u)
      (act (vlet (site L l) le) v) u v u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (fun b => X.op l 2 (X.op l 0 (u b))) (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      u (fun b => X.op l 5 (X.op l 3 (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v b))) (-t⁻¹) 1 h0
      (LC _ _ hu hv) (LC _ _ hu hE) (LC _ _ (hop2 2 0 u hu) hE) (LC _ _ hu (hop2 5 3 _ hE))
      (hL2 _ _ hu hv) (hL2 _ _ hu hE) (hL2 _ _ (hop2 2 0 u hu) hE) (hL2 _ _ hu (hop2 5 3 _ hE))
      (fun c' g => by
        simp only [hsSum]
        rw [sumPt_minus X L hAL l le hp hY u v _ (by rw [glue_succ_self]; exact ht) (Matrix.of g), glue_succ_self]
        ring)
    have hleib := (hLb u _ hu hE).1
    have hpr := hprod true
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, one_mul] at hpr ⊢
    generalize wirt true (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c) t = wD at hpr ⊢
    simp only [Dens] at hpr ⊢
    rw [hform]
    generalize ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) = W at hpr hq ⊢
    generalize form μ l.succ u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (Function.update c l t) = F at hpr hleib ⊢
    have hct2 : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
    linear_combination W * hpr - W * hleib + wD * hq + W * F * t⁻¹ * hq - W * F * conj t * W * hct2
  ·
    have hform := form_comb μ hμ l.succ (Function.update c l t) (act (ivlet (site L l) le) u)
      (act (vlet (site L l) le) v) u v u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (fun b => X.op l 5 (X.op l 3 (u b))) (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      u (fun b => X.op l 2 (X.op l 0 (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v b))) (conj t)⁻¹ (-1) h0
      (LC _ _ hu hv) (LC _ _ hu hE) (LC _ _ (hop2 5 3 u hu) hE) (LC _ _ hu (hop2 2 0 _ hE))
      (hL2 _ _ hu hv) (hL2 _ _ hu hE) (hL2 _ _ (hop2 5 3 u hu) hE) (hL2 _ _ hu (hop2 2 0 _ hE))
      (fun c' g => by
        simp only [hsSum]
        rw [sumPt_plus X L hAL l le hp hY u v _ (by rw [glue_succ_self]; exact ht) (Matrix.of g), glue_succ_self]
        ring)
    have hleib := (hLb u _ hu hE).2
    have hpr := hprod false
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpr ⊢
    generalize wirt false (Dens μ l u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v) c) t = wD at hpr ⊢
    simp only [Dens] at hpr ⊢
    rw [hform]
    generalize ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) = W at hpr hq ⊢
    generalize form μ l.succ u (act (eU le.intersection_update_fsHerm_neg_one 1 0 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) v)
      (Function.update c l t) = F at hpr hleib ⊢
    have hct : (conj t)⁻¹ * conj t = 1 := inv_mul_cancel₀ ((map_ne_zero _).mpr ht)
    linear_combination -W * hpr + W * hleib - wD * hq - W * F * (conj t)⁻¹ * hq + W * F * t * W * hct

end Core

end OneLetterPf

open OneLetterPf in

theorem one_letter_density_estimate (hL : LeibnizCls) (hS : DensSmoothCls) : OneLetterDens := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl le hre
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hY : conj le.pt = le.pt := Complex.conj_eq_iff_im.mpr hre
  refine ⟨if le.plus then -1 else 1, !le.plus, 1, 0, fun u v hu hv c hc t ht => ?_⟩
  have hS' := fun (x y : Ix S → RadSp P.k P.r z z' π π') (hx : ∀ b, x b ∈ ClsE S P z z' π π' X L st l0 D l)
      (hy : ∀ b, y b ∈ ClsE S P z z' π π' X L st l0 D l) =>
    hS Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl x y hx hy c hc
  exact core X L hD.2.2.1 μ hD.2.1 l le hY (ClsE S P z z' π π' X L st l0 D l)
    (fun j Φ hΦ => clsE_op P z z' π π' X L st l0 D l j hΦ)
    (clsE_lc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l) c t ht
    (fun x y hx hy b => (hS' x y hx hy).2 t ht b)
    (fun x y hx hy => (((hS' x y hx hy).1 1).contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds ht)).differentiableAt (by norm_num))
    (fun x y hx hy => hL Wp Wq S P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' l hl x y hx hy c hc t ht)
    u v hu hv

end Formalism.FourierDecayAlt.P.CutSE
