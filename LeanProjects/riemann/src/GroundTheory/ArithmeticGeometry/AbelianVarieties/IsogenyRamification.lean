import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyValuation
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualIsogenyExists
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

namespace Isogeny

theorem divisorOf_comap (φ : Isogeny E E') {f : E'.toAffine.FunctionField} (hf : f ≠ 0)
    (R : E.toAffine.Point) :
    divisorOf E (φ.comap f) R = (φ.ramIdx : ℤ) * divisorOf E' f (φ.pointMap R) := by
  rw [divisorOf_apply, divisorOf_apply, φ.ordPoint_comap R hf]

end Isogeny

section Poly

variable (E)

theorem ordPoint_zero_poly {p : F[X]} (hp : p ≠ 0) :
    ordPoint E 0 (algebraMap F[X] E.toAffine.FunctionField p) = -2 * (p.natDegree : ℤ) := by
  have hvF : ∀ c : F, c ≠ 0 → valuationInfty E (algebraMap F E.toAffine.FunctionField c) = 1 :=
    fun c hc => valuationInfty_algebraMap_const_eq_one E hc
  have h := valuation_poly_of_one_lt (valuationInfty E) hvF two_pos (valuationInfty_genX E) hp
  have hne : algebraMap F[X] E.toAffine.FunctionField p ≠ 0 := by
    rw [← aeval_genX]; exact (aeval_genX_eq_zero_iff E p).not.mpr hp
  have h2 := valuationPoint_eq_exp E 0 hne
  rw [valuationPoint_zero_eq, h, exp_inj] at h2
  linarith

theorem ordPoint_some_poly_of_eval_ne {x₀ y₀ : F} (h : E.toAffine.Nonsingular x₀ y₀) {p : F[X]}
    (hp : p.eval x₀ ≠ 0) :
    ordPoint E (.some x₀ y₀ h) (algebraMap F[X] E.toAffine.FunctionField p) = 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hne : algebraMap F[X] E.toAffine.FunctionField p ≠ 0 := by
    rw [← aeval_genX]; exact (aeval_genX_eq_zero_iff E p).not.mpr hp0
  have hnot : algebraMap F[X] E.toAffine.CoordinateRing p ∉ (heightOneOfNonsingular h).asIdeal := by
    intro hmem
    have := XYIdeal_le_ker h.1 hmem
    rw [RingHom.mem_ker] at this
    apply hp
    rw [← this]
    show _ = evalPoint h.1 (AdjoinRoot.mk _ (C p))
    rw [evalPoint_mk, evalEval_C]
  have hv : valuationPoint E (.some x₀ y₀ h) (algebraMap F[X] E.toAffine.FunctionField p) = 1 := by
    show (heightOneOfNonsingular h).valuation _ _ = 1
    rw [IsScalarTower.algebraMap_apply F[X] E.toAffine.CoordinateRing E.toAffine.FunctionField,
      HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
    exact hnot
  have h2 := valuationPoint_eq_exp E (.some x₀ y₀ h) hne
  rw [hv, ← exp_zero, exp_inj] at h2
  linarith

omit [IsAlgClosed F] [DecidableEq F] in
theorem algebraMap_poly_ne_zero {p : F[X]} (hp : p ≠ 0) :
    algebraMap F[X] E.toAffine.FunctionField p ≠ 0 := by
  rw [← aeval_genX]; exact (aeval_genX_eq_zero_iff E p).not.mpr hp

theorem ordPoint_div (P : E.toAffine.Point) {f g : E.toAffine.FunctionField} (hf : f ≠ 0)
    (hg : g ≠ 0) : ordPoint E P (f / g) = ordPoint E P f - ordPoint E P g := by
  have := ordPoint_mul E P (div_ne_zero hf hg) hg
  rw [div_mul_cancel₀ f hg] at this
  linarith

end Poly

section Mul

variable (E)

theorem ramIdx_mulIsogeny_mul_card_ker (n : ℤ) (hn : n ≠ 0) :
    (mulIsogeny E n hn).ramIdx * Nat.card (mulIsogeny E n hn).pointHom.ker = n.natAbs ^ 2 := by
  classical
  set φ := mulIsogeny E n hn
  set e := φ.ramIdx
  have hΨ0 : E.ΨSq n ≠ 0 := ΨSq_ne_zero_of_ne_zero E hn
  have hΦ0 : E.Φ n ≠ 0 := by
    intro h
    have := E.natDegree_Φ n
    rw [h, natDegree_zero] at this
    have : 0 < n.natAbs ^ 2 := by have := Int.natAbs_pos.mpr hn; positivity
    omega
  set a := algebraMap F[X] E.toAffine.FunctionField (E.ΨSq n)
  set b := algebraMap F[X] E.toAffine.FunctionField (E.Φ n)
  have ha : a ≠ 0 := algebraMap_poly_ne_zero E hΨ0
  have hb : b ≠ 0 := algebraMap_poly_ne_zero E hΦ0
  have hx : φ.comap (genX E) = b / a := by
    rw [Isogeny.comap_genX, mulIsogeny_alt, aeval_genX, aeval_genX]
  have hgx : genX E ≠ 0 := genX_ne_zero' E
  have hordx : ordPoint E 0 (genX E) = -2 := by
    have := ordPoint_zero_poly E (p := X) X_ne_zero
    rw [natDegree_X] at this
    rw [genX_eq]; simpa using this
  have hker : ∀ T : E.toAffine.Point, T ∈ φ.pointHom.ker ↔ n • T = 0 := fun T => by
    rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny]

  have hO : (e : ℤ) = (n.natAbs ^ 2 : ℕ) - ((E.ΨSq n).natDegree : ℤ) := by
    have h1 := φ.ordPoint_comap 0 hgx
    rw [Isogeny.pointMap_mulIsogeny, smul_zero, hordx, hx, ordPoint_div E 0 hb ha,
      ordPoint_zero_poly E hΦ0, ordPoint_zero_poly E hΨ0, E.natDegree_Φ n] at h1
    linarith

  have hA : ∀ {x₀ y₀ : F} (h : E.toAffine.Nonsingular x₀ y₀),
      ordPoint E (.some x₀ y₀ h) a = if n • (Point.some x₀ y₀ h) = 0 then 2 * (e : ℤ) else 0 := by
    intro x₀ y₀ h
    split_ifs with hT
    · have hz : (E.ΨSq n).eval x₀ = 0 := (zsmul_eq_zero_iff E h n).mp hT
      have hΦe : (E.Φ n).eval x₀ ≠ 0 := by
        intro hΦ
        obtain ⟨u, v, huv⟩ := isCoprime_Φ_ΨSq E n
        have := congrArg (eval x₀) huv
        simp only [eval_add, eval_mul, hΦ, hz, mul_zero, add_zero, eval_one] at this
        exact zero_ne_one this
      have h1 := φ.ordPoint_comap (.some x₀ y₀ h) hgx
      rw [Isogeny.pointMap_mulIsogeny, hT, hordx, hx, ordPoint_div E _ hb ha,
        ordPoint_some_poly_of_eval_ne E h hΦe] at h1
      linarith
    · exact ordPoint_some_poly_of_eval_ne E h (fun hz => hT ((zsmul_eq_zero_iff E h n).mpr hz))

  have hfin : Set.Finite {T : E.toAffine.Point | n • T = 0} := by
    have : Finite φ.pointHom.ker := φ.finite_ker
    have h2 : ({T : E.toAffine.Point | n • T = 0} : Set E.toAffine.Point) = φ.pointHom.ker := by
      ext T; exact (hker T).symm
    rw [h2]
    exact Set.toFinite _
  set S := hfin.toFinset
  have hcard : Nat.card φ.pointHom.ker = S.card := by
    rw [← Nat.card_eq_card_finite_toFinset hfin]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun T => hker T)
  have h0S : (0 : E.toAffine.Point) ∈ S := by simp [S]
  set D : CurveDivisor E := (∑ T ∈ S.erase 0, Finsupp.single T (2 * (e : ℤ))) +
    Finsupp.single 0 (-2 * ((E.ΨSq n).natDegree : ℤ))
  have hD : divisorOf E a = D := by
    ext P
    rw [divisorOf_apply]
    simp only [D, Finsupp.add_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
    by_cases hP : P = 0
    · subst hP
      rw [Finset.sum_eq_zero (fun T hT => if_neg (Finset.ne_of_mem_erase hT)), if_pos rfl, zero_add,
        ordPoint_zero_poly E hΨ0]
    · rw [if_neg (Ne.symm hP), add_zero, Finset.sum_ite_eq']
      obtain ⟨h, hP'⟩ := eq_some_xOf_yOf E hP
      have hmem : P ∈ S.erase 0 ↔ n • P = 0 := by simp [S, hP]
      rw [hP', hA h, ← hP']
      by_cases hT : n • P = 0
      · rw [if_pos hT, if_pos (hmem.mpr hT)]
      · rw [if_neg hT, if_neg (fun h' => hT (hmem.mp h'))]
  have hdeg := divisorDegree_divisorOf E ha
  rw [hD, map_add, map_sum, divisorDegree_single] at hdeg
  simp only [divisorDegree_single, Finset.sum_const, Finset.card_erase_of_mem h0S, smul_eq_mul] at hdeg
  have hS : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, h0S⟩
  rw [hcard]
  rw [nsmul_eq_mul, Nat.cast_sub hS] at hdeg
  have h2 : 2 * ((e : ℤ) * S.card) = 2 * ((n.natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast at hdeg hO ⊢
    linear_combination hdeg + 2 * hO
  have h3 : (e : ℤ) * S.card = ((n.natAbs ^ 2 : ℕ) : ℤ) := by linarith
  exact_mod_cast h3

end Mul

section Dvd

theorem infinite_point (E : WeierstrassCurve F) [E.IsElliptic] : Infinite E.toAffine.Point := by
  have : Infinite F := infinite_of_isSepClosed F
  choose y hy using fun x : F => exists_equation E x
  refine Infinite.of_injective (fun x : F => Point.some x (y x)
    (equation_iff_nonsingular.mp (hy x))) fun a b hab => ?_
  simp only [Point.some.injEq] at hab
  exact hab.1

namespace Isogeny

theorem exists_ordPoint_eq_ite (S : Finset E.toAffine.Point) :
    ∃ t : E.toAffine.FunctionField, t ≠ 0 ∧
      ∀ T ∈ S, ordPoint E T t = if T = 0 then 1 else 0 := by
  have := infinite_point E
  obtain ⟨B, hB⟩ := Infinite.exists_notMem_finset S
  obtain ⟨C, hC⟩ := Infinite.exists_notMem_finset (S ∪ S.image (· - B))
  have hC1 : C ∉ S := fun h => hC (Finset.mem_union_left _ h)
  have hC2 : B + C ∉ S := fun h => hC (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨B + C, h, by abel⟩))
  set D : CurveDivisor E := Finsupp.single 0 1 + Finsupp.single (B + C) 1 - Finsupp.single B 1 -
    Finsupp.single C 1
  have hdeg : divisorDegree E D = 0 := by
    simp only [D, map_sub, map_add, divisorDegree_single]; norm_num
  have hsum : divisorSum E D = 0 := by
    simp only [D, map_sub, map_add, divisorSum_single, one_smul]; abel
  obtain ⟨t, ht, htD⟩ := exists_divisorOf_eq E hdeg hsum
  refine ⟨t, ht, fun T hT => ?_⟩
  rw [← divisorOf_apply, htD]
  have h1 : B + C ≠ T := fun h => hC2 (h ▸ hT)
  have h2 : B ≠ T := fun h => hB (h ▸ hT)
  have h3 : C ≠ T := fun h => hC1 (h ▸ hT)
  simp only [D, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply, if_neg h1, if_neg h2,
    if_neg h3]
  by_cases h0 : T = 0
  · subst h0; simp
  · rw [if_neg (Ne.symm h0), if_neg h0]; simp

theorem ramIdx_dvd_insepDeg (φ : Isogeny E E') : φ.ramIdx ∣ φ.insepDeg := by
  classical
  haveI := Fintype.ofFinite φ.pointHom.ker
  set S : Finset E.toAffine.Point := Finset.univ.image (fun T : φ.pointHom.ker => (T : E.toAffine.Point))
  obtain ⟨t, ht, hord⟩ := exists_ordPoint_eq_ite (E := E) S
  set u := ∏ T : φ.pointHom.ker, translate E T t
  have hu0 : u ≠ 0 := Finset.prod_ne_zero_iff.mpr fun T _ => translate_ne_zero E _ ht
  have hfix : u ∈ φ.fixedKer := by
    apply mem_fixedKer_of_forall
    intro R hR
    rw [map_prod]
    simp only [translate_translate]
    exact Fintype.prod_equiv (Equiv.addLeft (⟨R, hR⟩ : φ.pointHom.ker)) _ _ (fun T => rfl)
  have hu : ordPoint E 0 u = 1 := by
    rw [← divisorOf_apply, divisorOf_prod E _ _ (fun T _ => translate_ne_zero E _ ht),
      Finsupp.finset_sum_apply]
    have : ∀ T : φ.pointHom.ker, divisorOf E (translate E T t) 0 =
        if (T : E.toAffine.Point) = 0 then 1 else 0 := by
      intro T
      rw [divisorOf_apply, ordPoint_translate E 0 _ ht, zero_add,
        hord _ (Finset.mem_image_of_mem _ (Finset.mem_univ T))]
    simp only [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (Finset.univ.filter fun T : φ.pointHom.ker => (T : E.toAffine.Point) = 0) = {0} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    rw [this, Finset.card_singleton, Nat.cast_one]
  obtain ⟨g, hg⟩ := φ.exists_comap_eq_pow hfix
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm] at hg
    exact pow_ne_zero _ hu0 hg
  have h1 := φ.ordPoint_comap 0 hg0
  rw [hg, ← divisorOf_apply, divisorOf_pow E hu0, Finsupp.smul_apply, divisorOf_apply, hu,
    nsmul_eq_mul, mul_one, show φ.pointMap 0 = 0 from φ.pointHom.map_zero] at h1
  exact Int.natCast_dvd_natCast.mp ⟨_, h1⟩

end Isogeny

end Dvd

section Degree

namespace Isogeny

theorem card_ker_comp (ψ : Isogeny E' E'') (φ : Isogeny E E') :
    Nat.card (ψ.comp φ).pointHom.ker = Nat.card ψ.pointHom.ker * Nat.card φ.pointHom.ker := by
  set K := (ψ.comp φ).pointHom.ker
  have hK : ∀ T, T ∈ K ↔ φ.pointMap T ∈ ψ.pointHom.ker := fun T => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, pointHom_apply, pointHom_apply, pointMap_comp]
  let h : K →+ ψ.pointHom.ker :=
    { toFun := fun T => ⟨φ.pointMap T, (hK T).mp T.2⟩
      map_zero' := Subtype.ext (φ.pointHom.map_zero)
      map_add' := fun S T => Subtype.ext (φ.pointMap_add S T) }
  have hsurj : Function.Surjective h := by
    rintro ⟨S, hS⟩
    obtain ⟨T, rfl⟩ := φ.pointMap_surjective S
    exact ⟨⟨T, (hK T).mpr hS⟩, rfl⟩
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup h.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective h hsurj).toEquiv] at e1
  rw [e1]
  congr 1
  refine Nat.card_congr
    { toFun := fun x => ⟨x.1.1, by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this ⊢
        exact congrArg Subtype.val this⟩
      invFun := fun T => ⟨⟨T.1, (hK T.1).mpr (by
        rw [AddMonoidHom.mem_ker] at ⊢
        have := T.2
        rw [AddMonoidHom.mem_ker, pointHom_apply] at this
        rw [pointHom_apply, this]; exact ψ.pointHom.map_zero)⟩, by
        rw [AddMonoidHom.mem_ker]
        exact Subtype.ext (by have := T.2; rwa [AddMonoidHom.mem_ker] at this)⟩
      left_inv := fun x => rfl
      right_inv := fun T => rfl }

theorem ramIdx_eq_insepDeg (φ : Isogeny E E') : φ.ramIdx = φ.insepDeg := by
  set d := φ.degree
  have hd : (d : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr φ.degree_pos.ne'
  have hc := φ.dual_comp
  have he : φ.dual.ramIdx * φ.ramIdx = (mulIsogeny E d hd).ramIdx := by
    rw [← ramIdx_comp, hc]
  have hk : Nat.card φ.dual.pointHom.ker * Nat.card φ.pointHom.ker =
      Nat.card (mulIsogeny E d hd).pointHom.ker := by
    rw [← card_ker_comp, hc]
  have h1 := ramIdx_mulIsogeny_mul_card_ker E (d : ℤ) hd
  rw [Int.natAbs_natCast, ← he, ← hk] at h1
  have hq1 := φ.degree_eq_insepDeg_mul
  have hq2 := φ.dual.degree_eq_insepDeg_mul
  rw [degree_dual] at hq2
  have hk1 : 0 < Nat.card φ.pointHom.ker := Nat.card_pos
  have hk2 : 0 < Nat.card φ.dual.pointHom.ker := Nat.card_pos
  have heq : φ.dual.ramIdx * φ.ramIdx = φ.dual.insepDeg * φ.insepDeg := by
    have : (φ.dual.ramIdx * φ.ramIdx) * (Nat.card φ.dual.pointHom.ker * Nat.card φ.pointHom.ker) =
        (φ.dual.insepDeg * φ.insepDeg) *
          (Nat.card φ.dual.pointHom.ker * Nat.card φ.pointHom.ker) := by
      calc _ = d ^ 2 := by rw [← h1]
        _ = _ := by
          rw [sq]
          show φ.degree * φ.degree = _
          nth_rewrite 1 [hq2]
          rw [hq1]
          ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hk2 hk1) this
  have l1 := Nat.le_of_dvd φ.insepDeg_pos φ.ramIdx_dvd_insepDeg
  have l2 := Nat.le_of_dvd φ.dual.insepDeg_pos φ.dual.ramIdx_dvd_insepDeg
  have p1 := φ.ramIdx_pos
  have p2 := φ.dual.ramIdx_pos
  by_contra hne
  have hlt : φ.ramIdx < φ.insepDeg := lt_of_le_of_ne l1 hne
  have : φ.dual.ramIdx * φ.ramIdx < φ.dual.insepDeg * φ.insepDeg :=
    calc φ.dual.ramIdx * φ.ramIdx < φ.dual.ramIdx * φ.insepDeg := Nat.mul_lt_mul_of_pos_left hlt p2
      _ ≤ φ.dual.insepDeg * φ.insepDeg := Nat.mul_le_mul_right _ l2
  omega

theorem ramIdx_mul_card_ker (φ : Isogeny E E') : φ.ramIdx * Nat.card φ.pointHom.ker = φ.degree := by
  rw [ramIdx_eq_insepDeg, degree_eq_insepDeg_mul]

end Isogeny

end Degree

end GroundTheory.Arith.Abelian
