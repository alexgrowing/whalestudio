import Mathlib
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem frob_root_eq {F : Type} [Field F] {a b : F} {m n : ℕ} (hm : 0 < m) (hc : m.Coprime n)
    (ha : a ^ m = 1) (hb : b ^ m = 1) (h : a ^ n = b ^ n) : a = b := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hb
    exact zero_ne_one hb
  have h1 : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  have h2 : (a / b) ^ n = 1 := by rw [div_pow, h, div_self (pow_ne_zero _ hb0)]
  have h3 : orderOf (a / b) = 1 :=
    Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  exact (div_eq_one_iff_eq hb0).1 (orderOf_eq_one_iff.1 h3)

theorem IsFrac.frob_injective {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {a t : A}
    (hf : IsFrac f a t) (hi : Function.Injective f) {F : B →+* B} {g : A →+* A}
    (hF : ∀ x, F (f x) = f (g x)) (hg : Function.Injective g) : Function.Injective F := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, n, y, h⟩ := hf.2.2 x
  have h1 := congrArg F h
  rw [map_mul, hx, mul_zero, hF] at h1
  have hy : y = 0 := hg (hi (by rw [← h1, map_zero, map_zero]))
  rw [hy, map_zero] at h
  exact ((hf.1.pow m).mul (hf.2.1.pow n)).mul_right_eq_zero.1 h

theorem frob_injective_of_fac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) (hg : Function.Injective g) :
    Function.Injective f := fun x y e => hg (by rw [← h, ← h, e])

theorem frob_fix_padic {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (F : B →+* B)
    (q : ℚ_[l] →+* B) (h : ∀ z : ℤ_[l], F (q (z : ℚ_[l])) = q (z : ℚ_[l])) (x : ℚ_[l]) :
    F (q x) = q x :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := F.comp q) (k := q) (RingHom.ext h)) x

theorem frob_map_mul_natCast {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) (x : A) :
    f ((n : A) * x) = (n : B) * f x := by
  rw [map_mul, map_natCast]

theorem frob_not_mem_sq {R : Type} [CommRing R] [IsDomain R] {t : R} (ht : Irreducible t) :
    t ∉ Ideal.span {t} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  have h : t * (t * c) = t * 1 := by rw [mul_one, ← mul_assoc, ← sq, ← hc]
  exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ ht.ne_zero h))

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem frob_oD_apply (x : Om l) :
    oD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (algClToBdR l x) := rfl

theorem frob_qB_coe (z : ℤ_[l]) : qB l (z : ℚ_[l]) = Per6.cB l (algebraMap (AInf ℂ_[l] l)
    (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z)) := by
  apply ιCD_injective
  refine (ιCD_qB _).trans (Eq.trans ?_ (ιCD_cB _).symm)
  rw [cD_apply, ACris.iota_padicInt, frob_oD_apply, AlgHom.commutes]

theorem frob_phi_padicInt (z : ℤ_[l]) :
    ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (IsPerfectoidField.padicIntToWitt l z)) =
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (IsPerfectoidField.padicIntToWitt l z) := by
  rw [ACris.phi_algebraMap, ACris.frobenius_padicIntToWitt]

theorem φB_qB (q : ℚ_[l]) : Per6.φB l (qB l q) = qB l q :=
  frob_fix_padic (Per6.φB l) (qB l) (fun z =>
    (congrArg (Per6.φB l) (frob_qB_coe z)).trans (((φB_cB _).trans
      (congrArg (Per6.cB l) (frob_phi_padicInt z))).trans (frob_qB_coe z).symm)) q

theorem isUnit_tB : IsUnit (tB l) := (cB_isFrac l).2.1

theorem frob_phi_tA : ACris.phi ℂ_[l] l (Per6.tA l) = (l : ACris.ACris ℂ_[l] l) * Per6.tA l :=
  ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))

theorem φB_tB : Per6.φB l (tB l) = (l : Per6.Bcris l) * tB l :=
  ((φB_cB (Per6.tA l)).trans (congrArg (Per6.cB l) frob_phi_tA)).trans
    (frob_map_mul_natCast (Per6.cB l) l (Per6.tA l))

theorem ιCD_tB : ιCD l (tB l) = algebraMap (Per6.BdRp l) (Per6.BdR l) (tBdR l) :=
  (ιCD_cB (Per6.tA l)).trans (cD_tA l)

theorem ιCD_tB_mem : ιCD l (tB l) ∈ Per6.FilD l 1 := by
  rw [ιCD_tB]
  refine (IsPerfectoidField.algebraMap_mem_fil_iff (K := ℂ_[l]) (p := l) (tBdR l) 1).2 ?_
  rw [pow_one, maximalIdeal_eq_span_tBdR]
  exact Ideal.mem_span_singleton_self _

theorem ιCD_tB_not_mem : ιCD l (tB l) ∉ Per6.FilD l 2 := by
  rw [ιCD_tB]
  intro h
  have h1 := (IsPerfectoidField.algebraMap_mem_fil_iff (K := ℂ_[l]) (p := l) (tBdR l) 2).1 h
  rw [maximalIdeal_eq_span_tBdR] at h1
  exact frob_not_mem_sq irreducible_tBdR h1

theorem frob_cB_injective : Function.Injective (Per6.cB l) :=
  frob_injective_of_fac (ιCD_fac l) (cD_injective l)

theorem φB_injective_of (h : Function.Injective (ACris.phi ℂ_[l] l)) :
    Function.Injective (Per6.φB l) :=
  (cB_isFrac l).frob_injective frob_cB_injective φB_cB h

theorem frob_aB_apply (a : Ainf l) : Per6.aB l a =
    Per6.cB l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) :=
  (RingHom.comp_apply _ _ a).trans (RingHom.comp_apply _ _ _)

theorem frob_coeff_tiltMap (xb : OCb l) (k : ℕ) (y : OC l)
    (h : PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    PreTilt.coeff k (Per6.tiltMap l xb) = Ideal.Quotient.mk _ (Per6.intEquiv l y) :=
  (show PreTilt.coeff k (Per6.tiltMap l xb) = Per6.modPEquiv l (PreTilt.coeff k xb) from rfl).trans
    ((congrArg (Per6.modPEquiv l) h).trans rfl)

theorem frob_tilt_root {c : ℂ_[l]} {m : ℕ} (hm : 0 < m) (hc : m.Coprime l)
    (x : PreTilt ↥(normInteger ℂ_[l]) l) (y : ℕ → ↥(normInteger ℂ_[l]))
    (h1 : ∀ k, (y k : ℂ_[l]) ^ (l ^ k) = c) (h2 : ∀ k, y k ^ m = 1)
    (h3 : ∀ k, PreTilt.coeff k x = Ideal.Quotient.mk _ (y k)) :
    x ^ m = 1 ∧ ((PreTilt.untilt x : ↥(normInteger ℂ_[l])) : ℂ_[l]) = c := by
  have h2' : ∀ k, (y k : ℂ_[l]) ^ m = 1 := fun k => by
    have := congrArg Subtype.val (h2 k)
    simpa using this
  have hy : ∀ n, y (n + 1) ^ l = y n := fun n => Subtype.ext (by
    rw [SubmonoidClass.coe_pow]
    refine frob_root_eq hm (hc.pow_right n) ?_ (h2' n) ?_
    · rw [← pow_mul, mul_comm, pow_mul, h2', one_pow]
    · rw [← pow_mul, ← pow_succ', h1, h1])
  have hx : x = IsPerfectoidField.ofCompatible l y hy := IsPerfectoidField.preTilt_ext l fun n => by
    rw [h3, IsPerfectoidField.coeff_ofCompatible]
  refine ⟨IsPerfectoidField.preTilt_ext l fun n => ?_, ?_⟩
  · rw [map_pow, h3, ← map_pow, h2, map_one, map_one]
  · rw [hx, IsPerfectoidField.untilt_ofCompatible, ← h1 0, pow_zero, pow_one]

theorem frob_iota_teich {ζ : PadicAlgCl l} {m : ℕ} (hm : 0 < m) (hζ : ζ ^ m = 1)
    (x : PreTilt ↥(normInteger ℂ_[l]) l) (hx : x ^ m = 1)
    (hu : ((PreTilt.untilt x : ↥(normInteger ℂ_[l])) : ℂ_[l]) = (ζ : ℂ_[l])) :
    ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
      (WittVector.teichmuller l x)) = algClToBdR l ζ := by
  have hζ0 : (ζ : ℂ_[l]) ≠ 0 := by
    intro h
    have := ACris.norm_eq_one_of_pow_eq_one hm (show (ζ : ℂ_[l]) ^ m = 1 by
      rw [PadicComplex.coe_eq, ← map_pow, hζ, map_one])
    rw [h, norm_zero] at this
    exact zero_ne_one this
  apply ACris.eq_of_pow_eq_one_of_theta_eq hm
  · rw [← map_pow, ← map_pow, ← map_pow, hx, map_one, map_one, map_one]
  · rw [← map_pow, hζ, map_one]
  · rw [thetaAlgHom_apply, ACris.thetaField_iota, ACris.theta_algebraMap,
      WittVector.fontaineTheta_teichmuller, hu, thetaAlgHom_algClToBdR]
  · rw [thetaAlgHom_algClToBdR]; exact hζ0

theorem frob_ainfMap_teich (xb : OCb l) :
    Per6.ainfMap l (WittVector.teichmuller l xb) = WittVector.teichmuller l (Per6.tiltMap l xb) :=
  WittVector.map_teichmuller l _ _

theorem aB_teich (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : (c : Om l) ^ m = 1)
    (xb : OCb l)
    (hx : ∀ k : ℕ, ∃ y : OC l, (y : ℂ_[l]) ^ (l ^ k) = ((c : Om l) : ℂ_[l]) ∧ y ^ m = 1 ∧
      PreTilt.coeff k xb = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) y) :
    Per6.aB l (WittVector.teichmuller l xb) = uB l c := by
  choose y h1 h2 h3 using hx
  have hco : m.Coprime l := ((Fact.out : l.Prime).coprime_iff_not_dvd.2 hl).symm
  obtain ⟨hp, hu⟩ := frob_tilt_root hm hco (Per6.tiltMap l xb) (fun k => Per6.intEquiv l (y k)) h1
    (fun k => by rw [← map_pow, h2, map_one]) (fun k => frob_coeff_tiltMap xb k (y k) (h3 k))
  apply ιCD_injective
  refine ((congrArg (ιCD l) (frob_aB_apply _)).trans (ιCD_cB _)).trans (Eq.trans ?_ (ιCD_uB c).symm)
  rw [cD_apply, frob_oD_apply, frob_ainfMap_teich, frob_iota_teich hm hc _ hp hu]

theorem frob_ainfMap_frobenius (a : Ainf l) :
    Per6.ainfMap l (WittVector.frobenius a) = WittVector.frobenius (Per6.ainfMap l a) := by
  ext n
  simp [Per6.ainfMap, WittVector.map_coeff, WittVector.coeff_frobenius_charP]

theorem frob_phi_ainfMap (a : Ainf l) :
    algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l (WittVector.frobenius a)) =
      ACris.phi ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l) (Per6.ainfMap l a)) := by
  rw [ACris.phi_algebraMap, frob_ainfMap_frobenius]
  rfl

theorem aB_frobenius (a : Ainf l) : Per6.aB l (WittVector.frobenius a) = Per6.φB l (Per6.aB l a) :=
  ((frob_aB_apply _).trans (congrArg (Per6.cB l) (frob_phi_ainfMap a))).trans
    ((φB_cB _).symm.trans (congrArg (Per6.φB l) (frob_aB_apply a).symm))

end PositivityTheory.LocInh
