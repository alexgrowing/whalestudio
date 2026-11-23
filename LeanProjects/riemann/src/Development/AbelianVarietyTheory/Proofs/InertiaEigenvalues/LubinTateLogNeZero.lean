import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.AdicMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open scoped Formalism.Per

namespace GlobalTheory.LogFirstOrder

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

abbrev Q : Type := AK K ⧸ RingHom.ker (thetaK K) ^ 2

abbrev QP : Type := Localization.Away ((l : ℕ) : Q K)

variable {K}

theorem l_ne_zero_OC : ((l : ℕ) : Per.OC l) ≠ 0 := by
  intro h
  apply GlobalTheory.RingBasics.p_ne_zero (p := l)
  rw [← map_natCast (algebraMap (Per.OC l) ℂ_[l]), h, map_zero]

theorem theta_eq_zero_of_pow_mul {n : ℕ} {c : AK K} (h : thetaK K ((l : AK K) ^ n * c) = 0) : thetaK K c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ l_ne_zero_OC)

theorem eq_zero_OC {t : Per.OC l} (h : ∀ n : ℕ, ((l : ℕ) : Per.OC l) ^ n ∣ t) : t = 0 :=
  GlobalTheory.DiscEval.eq_zero_of_dvd (p := l) h

variable (K) in
theorem exists_gen : ∃ η : AK K, RingHom.ker (thetaK K) = Ideal.span {η} := by
  obtain ⟨π, hπ⟩ := exists_unif (K := K)
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (thetaK K (inO K π))
  exact ⟨_, ker_thetaK hπ (hp.trans (thetaK_inO π))⟩

theorem step {η : AK K} (hI : RingHom.ker (thetaK K) = Ideal.span {η}) (hη : η ≠ 0) {a c d : AK K} {n : ℕ}
    (h : η * a = (l : AK K) ^ n * c + η ^ 2 * d) : ∃ c', a = (l : AK K) ^ n * c' + η * d := by
  have hθη : thetaK K η = 0 := by
    have : η ∈ RingHom.ker (thetaK K) := by rw [hI]; exact Ideal.mem_span_singleton_self η
    exact this
  have h1 : thetaK K ((l : AK K) ^ n * c) = 0 := by
    have := congrArg (thetaK K) h
    rw [map_mul, hθη, zero_mul, map_add, map_mul (thetaK K) (η ^ 2), map_pow, hθη] at this
    simpa using this.symm
  have hc : c ∈ Ideal.span {η} := by rw [← hI]; exact theta_eq_zero_of_pow_mul h1
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hc
  refine ⟨c', ?_⟩
  have h2 : η * (a - ((l : AK K) ^ n * c' + η * d)) = 0 := by
    rw [← hc'] at h
    linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left hη)

theorem theta_eq_zero_of_sq {a : AK K} (h : a ∈ RingHom.ker (thetaK K) ^ 2) : thetaK K a = 0 :=
  RingHom.mem_ker.1 (Ideal.pow_le_self two_ne_zero h)

theorem mem_sq_of_forall {a : AK K}
    (h : ∀ n : ℕ, ∃ c : AK K, a - (l : AK K) ^ n * c ∈ RingHom.ker (thetaK K) ^ 2) :
    a ∈ RingHom.ker (thetaK K) ^ 2 := by
  obtain ⟨η, hI⟩ := exists_gen K
  have hmem : ∀ z : AK K, thetaK K z = 0 ↔ η ∣ z := fun z => by
    rw [← Ideal.mem_span_singleton, ← hI, RingHom.mem_ker]
  have hsq : ∀ z : AK K, z ∈ RingHom.ker (thetaK K) ^ 2 ↔ η ^ 2 ∣ z := fun z => by
    rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  by_cases hη : η = 0
  · have := GlobalTheory.AinfK.complete_l K
    have h0 : a = 0 := GlobalTheory.DiscEval.eq_zero_of_dvd (p := l) fun n => by
      obtain ⟨c, hc⟩ := h n
      rw [hsq, hη, zero_pow two_ne_zero, zero_dvd_iff, sub_eq_zero] at hc
      exact ⟨c, hc⟩
    rw [h0]
    exact zero_mem _
  have h1 : thetaK K a = 0 := eq_zero_OC fun n => by
    obtain ⟨c, hc⟩ := h n
    have := theta_eq_zero_of_sq hc
    rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at this
    exact ⟨_, this⟩
  obtain ⟨b, rfl⟩ := (hmem a).1 h1
  have h2 : thetaK K b = 0 := eq_zero_OC fun n => by
    obtain ⟨c, hc⟩ := h n
    obtain ⟨d, hd⟩ := (hsq _).1 hc
    obtain ⟨c', hc'⟩ := step hI hη (a := b) (c := c) (d := d) (n := n) (by linear_combination hd)
    refine ⟨thetaK K c', ?_⟩
    rw [hc', map_add, map_mul, map_pow, map_natCast, (hmem _).2 (dvd_mul_right η d), add_zero]
  obtain ⟨e, rfl⟩ := (hmem b).1 h2
  exact (hsq _).2 ⟨e, by ring⟩

theorem mem_sq_of_l_mul {a : AK K} (h : (l : AK K) * a ∈ RingHom.ker (thetaK K) ^ 2) :
    a ∈ RingHom.ker (thetaK K) ^ 2 := by
  obtain ⟨η, hI⟩ := exists_gen K
  have hmem : ∀ z : AK K, thetaK K z = 0 ↔ η ∣ z := fun z => by
    rw [← Ideal.mem_span_singleton, ← hI, RingHom.mem_ker]
  have hsq : ∀ z : AK K, z ∈ RingHom.ker (thetaK K) ^ 2 ↔ η ^ 2 ∣ z := fun z => by
    rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 : thetaK K a = 0 :=
    theta_eq_zero_of_pow_mul (n := 1) (by rw [pow_one]; exact theta_eq_zero_of_sq h)
  obtain ⟨b, rfl⟩ := (hmem a).1 h1
  by_cases hη : η = 0
  · rw [hη, zero_mul]
    exact zero_mem _
  obtain ⟨d, hd⟩ := (hsq _).1 h
  have h3 : (l : AK K) * b = η * d := mul_left_cancel₀ hη (by linear_combination hd)
  have h2 : thetaK K b = 0 :=
    theta_eq_zero_of_pow_mul (n := 1) (by rw [pow_one, h3]; exact (hmem _).2 (dvd_mul_right η d))
  obtain ⟨e, rfl⟩ := (hmem b).1 h2
  exact (hsq _).2 ⟨e, by ring⟩

theorem eq_zero_of_l_mul_quot {q : Q K} (h : ((l : ℕ) : Q K) * q = 0) : q = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← map_natCast (Ideal.Quotient.mk (RingHom.ker (thetaK K) ^ 2)), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h
  exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_sq_of_l_mul h)

theorem eq_zero_of_forall_dvd {q : Q K} (h : ∀ n : ℕ, ((l : ℕ) : Q K) ^ n ∣ q) : q = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine Ideal.Quotient.eq_zero_iff_mem.2 (mem_sq_of_forall fun n => ?_)
  obtain ⟨w, hw⟩ := h n
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  rw [map_sub, map_mul, map_pow, map_natCast, hw, sub_self]

omit hl in

theorem precomplete_quot {A : Type} [CommRing A] (J : Ideal A) [IsPrecomplete (Ideal.span {(l : A)}) A] :
    IsPrecomplete (Ideal.span {((l : ℕ) : A ⧸ J)}) (A ⧸ J) where
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hf ⊢
    choose e he using fun n => hf (Nat.le_succ n)
    choose e' he' using fun n => Ideal.Quotient.mk_surjective (e n)
    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f 0)
    have hf' : ∀ n, f n = Ideal.Quotient.mk J (g - ∑ k ∈ Finset.range n, (l : A) ^ k * e' k) := fun n => by
      induction n with
      | zero => simp [hg]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← sub_sub, map_sub, ← ih, map_mul, map_pow, map_natCast, he', ← he]
        ring
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : A)})
      (fun n => g - ∑ k ∈ Finset.range n, (l : A) ^ k * e' k) fun {m n} hmn => by
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton]
        rw [sub_sub_sub_cancel_left, ← Finset.sum_Ico_eq_sub _ hmn]
        exact Finset.dvd_sum fun k hk => (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1).mul_right _
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hL
    refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
    have := map_dvd (Ideal.Quotient.mk J) (hL n)
    rwa [map_pow, map_natCast, map_sub, ← hf'] at this

variable (K)

instance complete_quot : IsAdicComplete (Ideal.span {((l : ℕ) : Q K)}) (Q K) :=
  have := GlobalTheory.AinfK.complete_l K
  { precomplete_quot (l := l) (RingHom.ker (thetaK K) ^ 2) with
    haus' := fun q hq => eq_zero_of_forall_dvd fun n => by
      have := hq n
      rwa [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this }

theorem isUnit_l_quot : IsUnit ((l : ℕ) : QP K) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := QP K) ((l : ℕ) : Q K)
  rwa [map_natCast] at h

theorem quot_injective : Function.Injective (algebraMap (Q K) (QP K)) :=
  IsLocalization.injective (M := Submonoid.powers ((l : ℕ) : Q K)) (QP K) (Submonoid.powers_le.2
    (mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_l_mul_quot h))

def psiA : Per.Ainf l →+* Q K := (Ideal.Quotient.mk _).comp (inA K)

def lam : Per.AinfP l →+* QP K :=
  IsLocalization.Away.lift ((l : ℕ) : Per.Ainf l) (g := (algebraMap (Q K) (QP K)).comp (psiA K)) (by
    rw [map_natCast]; exact isUnit_l_quot K)

theorem lam_alg (a : Per.Ainf l) :
    lam K (algebraMap (Per.Ainf l) (Per.AinfP l) a) = algebraMap (Q K) (QP K) (psiA K a) :=
  IsLocalization.Away.lift_eq _ _ a

theorem lam_mem (y : Per.AinfP l) (hy : y ∈ Per.Acris0 l) : lam K y ∈ (algebraMap (Q K) (QP K)).range := by
  let S : Subalgebra (Per.Ainf l) (Per.AinfP l) :=
    { ((algebraMap (Q K) (QP K)).range.comap (lam K)).toSubsemiring with
      algebraMap_mem' := fun r => ⟨psiA K r, (lam_alg K r).symm⟩ }
  refine GlobalTheory.RingIface.acris0_le l S (fun x hx n y hn => ?_) hy
  · change lam K y ∈ (algebraMap (Q K) (QP K)).range
    have hxK : inA K x ∈ RingHom.ker (thetaK K) := by rw [RingHom.mem_ker, thetaK_inA]; exact hx
    have hnu : IsUnit ((n.factorial : ℕ) : QP K) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial (Nat.factorial_ne_zero n)).map (lam K)
      rwa [map_natCast] at this
    have e := congrArg (lam K) hn
    rw [map_mul, map_natCast, map_pow, lam_alg] at e
    rcases n with _ | _ | n
    · exact ⟨1, by simpa using e.symm⟩
    · exact ⟨psiA K x, by simpa using e.symm⟩
    · refine ⟨0, ?_⟩
      have h0 : psiA K x ^ (n + 1 + 1) = 0 := by
        rw [psiA, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow hxK _)
      rw [← map_pow, h0, map_zero] at e
      rw [map_zero]
      exact (hnu.mul_right_eq_zero.1 e).symm

def equivRange : Q K ≃+* (algebraMap (Q K) (QP K)).range :=
  RingEquiv.ofBijective (algebraMap (Q K) (QP K)).rangeRestrict
    ⟨fun _ _ h => quot_injective K (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

def sig0 : Per.Acris0 l →+* Q K :=
  (equivRange K).symm.toRingHom.comp
    (((lam K).comp (Per.Acris0 l).val.toRingHom).codRestrict _ fun y => lam_mem K y.1 y.2)

theorem algebraMap_first_order_log (y : Per.Acris0 l) : algebraMap (Q K) (QP K) (sig0 K y) = lam K y :=
  congrArg Subtype.val ((equivRange K).apply_symm_apply ⟨lam K y, lam_mem K y.1 y.2⟩)

def sig : Per.Acris l →+* Q K :=
  (AdicCompletion.ofAlgEquiv (Ideal.span {((l : ℕ) : Q K)})).symm.toAlgHom.toRingHom.comp
    ((GlobalTheory.AdicMaps.padicMap l (sig0 K)).comp (GlobalTheory.AdicMaps.exists_acris_completion l).choose.toRingHom)

theorem sig_aC (a : Per.Ainf l) : sig K (aC l a) = psiA K a := by
  have h0 : (GlobalTheory.AdicMaps.exists_acris_completion l).choose (aC l a) =
      algebraMap (Per.Acris0 l) (AdicCompletion (Ideal.span {(l : Per.Acris0 l)}) (Per.Acris0 l)) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) := by
    rw [← (GlobalTheory.AdicMaps.exists_acris_completion l).choose_spec, ← GlobalTheory.RingIface.tower]
  have h2 : sig0 K (algebraMap _ (Per.Acris0 l) a) = psiA K a :=
    quot_injective K ((algebraMap_first_order_log K _).trans (lam_alg K a))
  change (AdicCompletion.ofAlgEquiv (Ideal.span {((l : ℕ) : Q K)})).symm
    (GlobalTheory.AdicMaps.padicMap l (sig0 K) ((GlobalTheory.AdicMaps.exists_acris_completion l).choose (aC l a))) = _
  rw [h0, GlobalTheory.AdicMaps.padicMap_alg, h2]
  exact AdicCompletion.ofAlgEquiv_symm_of _ _

def rhoC : CK K →+* Q K :=
  GlobalTheory.AcrisK.lift (sig K) ((Ideal.Quotient.mk _).comp (inO K)) fun w => by
    rw [sig_aC, psiA, RingHom.comp_apply, RingHom.comp_apply]
    exact congrArg _ (inA_wA K w)

theorem rhoC_ofA (z : AK K) : rhoC K (ofA K z) = Ideal.Quotient.mk _ z := by
  refine RingHom.congr_fun (GlobalTheory.AinfK.ringHom_ext (u := (rhoC K).comp (ofA K)) (v := Ideal.Quotient.mk _)
    (fun a => ?_) (fun c => ?_)) z
  · rw [RingHom.comp_apply, ofA_inA, rhoC, GlobalTheory.AcrisK.lift_inC, sig_aC]; rfl
  · rw [RingHom.comp_apply, ofA_inO, rhoC, GlobalTheory.AcrisK.lift_inI]; rfl

def rhoB : GlobalTheory.AcrisK.BK K →+* QP K := awayLift ((algebraMap (Q K) (QP K)).comp (rhoC K)) (isUnit_l_quot K)

theorem rhoB_toB (z : CK K) : rhoB K (toB K z) = algebraMap (Q K) (QP K) (rhoC K z) := awayLift_toB _ _ z

variable {K} in

theorem mem_sq_of_ev {L : PowerSeries ↥K.1} (h0 : PowerSeries.coeff 0 L = 0) (h1 : PowerSeries.coeff 1 L = 1)
    {x : AK K} (hx : thetaK K x = 0) (ev : Ev L x 0) : x ∈ RingHom.ker (thetaK K) ^ 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hx2 : rhoB K (toB K (ofA K x)) ^ 2 = 0 := by
    rw [rhoB_toB, rhoC_ofA, ← map_pow, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (RingHom.mem_ker.2 hx) 2), map_zero]
  refine eq_zero_of_forall_dvd fun r => ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∃ z : CK K,
      GlobalTheory.DiscEval.psum (inK K) L (toB K (ofA K x)) n - 0 = toB K ((l : CK K) ^ r * z) := ev r
  obtain ⟨z, hz⟩ := hN (N + 1 + 1) (by omega)
  have e := congrArg (rhoB K) hz
  rw [sub_zero, GlobalTheory.DiscEval.psum, Finset.sum_range_succ', Finset.sum_range_succ', h0, zero_add, h1, map_zero,
    zero_mul, add_zero, map_one, one_mul, pow_one, map_add, map_sum, Finset.sum_eq_zero, zero_add, rhoB_toB,
    rhoB_toB, rhoC_ofA, map_mul, map_pow, map_natCast] at e
  · exact ⟨_, quot_injective K e⟩
  · intro k _
    rw [map_mul, map_pow, add_assoc, pow_add, hx2, mul_zero, mul_zero]

theorem ltLog_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (hπ : Irreducible π)
    (f : PowerSeries ↥(OL K)) (hf : IsLubinTateSeries π f) (x : AK K) (hx : thetaK K x = 0),
    x ∉ RingHom.ker (thetaK K) ^ 2 → ltLog hπ hf x hx ≠ 0 := by
  intro l _ K π hπ f hf x hx hnot h0
  have ev := ev_ltLog hπ hf x hx
  rw [h0] at ev
  exact hnot (mem_sq_of_ev
    ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (GlobalTheory.LTLog.constantCoeff_log _ hπ hf))
    (GlobalTheory.LTLog.coeff_one_log _ hπ hf) hx ev)

end GlobalTheory.LogFirstOrder
