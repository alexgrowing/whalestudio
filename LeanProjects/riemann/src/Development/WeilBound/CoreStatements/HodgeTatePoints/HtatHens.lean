import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHensA

namespace PositivityTheory.HtPt.Htat.Hens

open CategoryTheory Polynomial IsLocalRing TensorProduct

section PiLocalization₂

variable {R : Type} [CommRing R] [IsDomain R] {S : Type} [CommRing S] [Algebra R S] [Algebra.Etale R S]

theorem stage_inj : Function.Injective (algebraMap S (S ⊗[R] FractionRing R)) :=
  Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R (FractionRing R))

theorem stage_int [IsIntegrallyClosed R] {z : S ⊗[R] FractionRing R} (hz : IsIntegral S z) :
    ∃ s, algebraMap S _ s = z := by
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S)
    (B := FractionRing R)).2 ⟨z, hz⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id S S) (integralClosure R (FractionRing R)).val t = z :=
    congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := R) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

omit [Algebra.Etale R S] in
theorem stage_den (z : S ⊗[R] FractionRing R) :
    ∃ (r : R) (y : S), r ≠ 0 ∧ algebraMap S _ y = algebraMap S _ (algebraMap R S r) * z := by
  induction z with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add x y hx hy =>
    obtain ⟨r, a, hr, ha⟩ := hx
    obtain ⟨s, b, hs, hb⟩ := hy
    refine ⟨r * s, algebraMap R S s * a + algebraMap R S r * b, mul_ne_zero hr hs, ?_⟩
    simp only [map_add, map_mul, ha, hb]
    ring
  | tmul x y =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hb
    refine ⟨b, a • x, nonZeroDivisors.ne_zero hb, ?_⟩
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [← Algebra.smul_def, smul_tmul, smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one,
      mul_div_cancel₀ _ hb']

theorem stage_reg (x : S ⊗[R] FractionRing R) : ∃ z, x * x * z = x := by
  let F := FractionRing R
  have : Module.Finite F (F ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free F _
  have : IsReduced (F ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field F _
  have : IsArtinianRing (F ⊗[R] S) := IsArtinianRing.of_finite F _
  let e := (Algebra.TensorProduct.comm R S F).toRingEquiv.trans (IsArtinianRing.equivPi (F ⊗[R] S)).toRingEquiv
  have key : ∀ y : (∀ m : MaximalSpectrum (F ⊗[R] S), (F ⊗[R] S) ⧸ m.asIdeal), ∃ w, y * y * w = y := fun y => by
    have : ∀ m, ∃ w, y m * y m * w = y m := fun m => by
      let _ := Ideal.Quotient.field m.asIdeal
      by_cases h : y m = 0
      · exact ⟨0, by simp [h]⟩
      · exact ⟨(y m)⁻¹, by rw [mul_assoc, mul_inv_cancel₀ h, mul_one]⟩
    choose w hw using this
    exact ⟨w, funext hw⟩
  obtain ⟨w, hw⟩ := key (e x)
  exact ⟨e.symm w, e.injective (by rw [map_mul, map_mul, e.apply_symm_apply, hw])⟩

theorem stage_idem [IsIntegrallyClosed R] (x : S) :
    ∃ (e y : S) (r : R), e * e = e ∧ e * x = x ∧ r ≠ 0 ∧ x * y = algebraMap R S r * e := by
  obtain ⟨z, hz⟩ := stage_reg (R := R) (algebraMap S (S ⊗[R] FractionRing R) x)
  have hi : IsIntegral S (algebraMap S (S ⊗[R] FractionRing R) x * z) :=
    ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_X]
      linear_combination z * hz⟩
  obtain ⟨e, he⟩ := stage_int hi
  obtain ⟨r, y, hr, hy⟩ := stage_den z
  refine ⟨e, y, r, stage_inj (R := R) ?_, stage_inj (R := R) ?_, hr, stage_inj (R := R) ?_⟩
  · rw [map_mul, he]; linear_combination z * hz
  · rw [map_mul, he]; linear_combination hz
  · rw [map_mul, map_mul, he, hy]; ring

end PiLocalization₂

namespace etaleColimit

open PointedEtale

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

theorem flat : Module.Flat R (etaleColimit R K) := by
  classical
  refine Module.Flat.of_forall_isTrivialRelation fun {l f x} h => ?_
  obtain ⟨X, hX⟩ := exists_of_finset (Finset.univ.image x)
  choose x' hx' using fun i => hX (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have h0 : of X (∑ i, f i • x' i) = of X 0 := by
    rw [map_zero, ← h, ← ofAlgHom_apply, map_sum]
    simp only [map_smul, ofAlgHom_apply, hx']
  obtain ⟨Y, g, hg⟩ := exists_hom_eq_of_of_eq h0
  rw [map_zero, map_sum] at hg
  simp only [map_smul] at hg
  obtain ⟨k, a, y, h1, h2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := Y) (f := f)
    (x := fun i => g.alg (x' i)) hg
  refine ⟨k, a, fun j => of Y (y j), fun i => ?_, h2⟩
  rw [← hx', ← of_map g, show g.alg (x' i) = _ from h1 i, ← ofAlgHom_apply, map_sum]
  simp only [map_smul, ofAlgHom_apply]

variable [IsDomain R]

theorem reg {r : R} (hr : r ≠ 0) {a : etaleColimit R K} (h : algebraMap R _ r * a = 0) : a = 0 := by
  have := flat (R := R) (K := K)
  have hreg : IsSMulRegular (etaleColimit R K) r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  exact hreg (show r • a = r • 0 by rw [smul_zero, Algebra.smul_def, h])

variable [IsIntegrallyClosed R]

theorem exists_dvd {a : etaleColimit R K} (ha : a ≠ 0) : ∃ (b : etaleColimit R K) (r : R), r ≠ 0 ∧
    a * b = algebraMap R _ r := by
  obtain ⟨X, x, rfl⟩ := exists_of a
  obtain ⟨e, y, r, h1, h2, hr, h3⟩ := stage_idem (R := R) x
  have he : of X e * (1 - of X e) = 0 := by rw [mul_sub, ← map_mul, h1, mul_one, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (of X e) with hu | hu
  · have : of X e = 1 := (sub_eq_zero.1 (hu.mul_right_eq_zero.1 he)).symm
    exact ⟨of X y, r, hr, by rw [← map_mul, h3, map_mul, this, mul_one, of_algebraMap]⟩
  · exact absurd (by rw [← h2, map_mul, hu.mul_left_eq_zero.1 he, zero_mul]) ha

theorem isDomain : IsDomain (etaleColimit R K) := by
  have : NoZeroDivisors (etaleColimit R K) := ⟨fun {a b} h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨c, r, hr, hc⟩ := exists_dvd ha
      exact Or.inr (reg hr (by rw [← hc]; linear_combination c * h))⟩
  exact NoZeroDivisors.to_isDomain _

theorem dvd_of_root {r : R} (hr : r ≠ 0) {h : etaleColimit R K} {p : (etaleColimit R K)[X]} (hp : p.Monic)
    (hz : (p.scaleRoots (algebraMap R _ r)).eval h = 0) : ∃ y, h = algebraMap R _ r * y := by
  obtain ⟨X₁, q₁, hq₁, rfl⟩ := exists_monic_lift p hp
  obtain ⟨X₂, x₂, rfl⟩ := exists_of h
  let X := tensor X₁ X₂
  let q : X.carrier[X] := q₁.map (inl X₁ X₂).alg.toRingHom
  have hq : q.Monic := hq₁.map _
  let x : X := (inr X₁ X₂).alg x₂
  have e1 : q.map (of X) = q₁.map (of X₁) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun a => of_map (inl X₁ X₂) a
  have e2 : of X x = of X₂ x₂ := of_map _ _
  have sc : ∀ {A B : Type} [CommRing A] [CommRing B] [Nontrivial B] (φ : A →+* B) (q : A[X]) (_ : q.Monic) (s a : A),
      φ ((q.scaleRoots s).eval a) = ((q.map φ).scaleRoots (φ s)).eval (φ a) := fun φ q hq s a => by
    rw [← map_scaleRoots _ _ _ (by rw [hq.leadingCoeff, map_one]; exact one_ne_zero), Polynomial.eval_map, eval₂_at_apply]
  have h0 : of X ((q.scaleRoots (algebraMap R X r)).eval x) = of X 0 := by
    rw [sc _ _ hq, e1, e2, of_algebraMap, hz, map_zero]
  obtain ⟨Y, g, hg⟩ := exists_hom_eq_of_of_eq h0
  have : Nontrivial Y := (of Y).domain_nontrivial
  have : Nontrivial (Y ⊗[R] FractionRing R) := (stage_inj (R := R) (S := Y)).nontrivial
  rw [map_zero] at hg
  let ι := algebraMap Y (Y ⊗[R] FractionRing R)
  let t : Y ⊗[R] FractionRing R := 1 ⊗ₜ (algebraMap R (FractionRing R) r)⁻¹
  have hrt : ι (algebraMap R Y r) * t = 1 := by
    have hr' : algebraMap R (FractionRing R) r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr
    simp only [ι, t, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul, Algebra.smul_def, mul_inv_cancel₀ hr']
    rfl
  let q' : Y.carrier[X] := q.map g.alg.toRingHom
  have hq' : q'.Monic := hq.map _
  have h1 : (q'.scaleRoots (algebraMap R Y r)).eval (g.alg x) = 0 := by
    have := sc g.alg.toRingHom q hq (algebraMap R X r) x
    rw [show g.alg.toRingHom (algebraMap R X r) = algebraMap R Y r from g.alg.commutes r] at this
    exact this.symm.trans hg
  have hi : IsIntegral Y (ι (g.alg x) * t) := by
    refine ⟨q', hq', ?_⟩
    have h2 := scaleRoots_eval₂_mul (p := q') ι (ι (g.alg x) * t) (algebraMap R Y r)
    rw [show ι (algebraMap R Y r) * (ι (g.alg x) * t) = ι (g.alg x) by linear_combination ι (g.alg x) * hrt,
      eval₂_at_apply, h1, map_zero] at h2
    exact ((IsUnit.of_mul_eq_one _ hrt).pow _).mul_right_eq_zero.1 h2.symm
  obtain ⟨y, hy⟩ := stage_int hi
  have h3 : g.alg x = algebraMap R Y r * y := stage_inj (R := R) (by
    rw [map_mul, hy]
    show ι _ = ι _ * _
    linear_combination (-ι (g.alg x)) * hrt)
  exact ⟨of Y y, by rw [← e2, ← of_map g, h3, map_mul, of_algebraMap]⟩

theorem isIntegrallyClosed : IsIntegrallyClosed (etaleColimit R K) := by
  have := isDomain (R := R) (K := K)
  let H := etaleColimit R K
  refine (isIntegrallyClosed_iff (FractionRing H)).2 fun {z} hz => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := H) z
  obtain ⟨c, r, hr, hc⟩ := exists_dvd (nonZeroDivisors.ne_zero hb)
  obtain ⟨p, hp, hz⟩ := hz
  have hinj := IsFractionRing.injective H (FractionRing H)
  have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing H) hb
  have e : algebraMap H (FractionRing H) (algebraMap R H r) *
      (algebraMap H (FractionRing H) a / algebraMap H (FractionRing H) b) = algebraMap H _ (a * c) := by
    rw [← hc, map_mul, map_mul, mul_right_comm, mul_div_cancel₀ _ hb']
  have h2 := scaleRoots_eval₂_eq_zero (algebraMap H (FractionRing H)) (s := algebraMap R H r) hz
  rw [e, eval₂_at_apply, map_eq_zero_iff _ hinj] at h2
  obtain ⟨y, hy⟩ := dvd_of_root hr hp h2
  refine ⟨y, ?_⟩
  have hr0 : algebraMap H (FractionRing H) (algebraMap R H r) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 fun h => one_ne_zero (reg hr (a := (1 : H)) (by rw [h, zero_mul]))
  exact mul_left_cancel₀ hr0 (by rw [e, hy, map_mul])

end etaleColimit

end PositivityTheory.HtPt.Htat.Hens

namespace PositivityTheory.HtPt.Htat

open Hens in
theorem hens_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : HenselianLocalRing R') (_ : Algebra R R'), IsIntegrallyClosed R' ∧ Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P := by
  intro R _ _ _ P _
  have hs : Function.Surjective (etaleColimit.toK : etaleColimit R P.ResidueField →+* P.ResidueField) := by
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ P) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hb' := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := P.ResidueField) hb
    have hk : ∀ c : R, algebraMap (R ⧸ P) P.ResidueField (Ideal.Quotient.mk P c) =
        etaleColimit.toK (algebraMap R (etaleColimit R P.ResidueField) c) := fun c => by
      rw [etaleColimit.toK_algebraMap]; rfl
    rw [hk] at hb'
    obtain ⟨t, ht⟩ := (etaleColimit.isUnit_of_toK_ne_zero hb').exists_right_inv
    refine ⟨algebraMap R _ a * t, ?_⟩
    have := congrArg etaleColimit.toK ht
    rw [map_mul, map_one] at this
    rw [hk, hk, map_mul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right this]
  refine ⟨etaleColimit R P.ResidueField, inferInstance, etaleColimit.isDomain, etaleColimit.henselianLocalRing hs,
    inferInstance, etaleColimit.isIntegrallyClosed, etaleColimit.flat, ?_⟩
  ext r
  refine Iff.trans ?_ (Ideal.algebraMap_residueField_eq_zero (I := P) (x := r))
  rw [← etaleColimit.toK_algebraMap, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    etaleColimit.isUnit_iff_toK_ne_zero, not_not]

end PositivityTheory.HtPt.Htat
