import Mathlib

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

theorem pow_le_comap_pow {I : Ideal A} {J : Ideal B} {f : A →+* B} (h : I ≤ J.comap f) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap f :=
  (Ideal.pow_right_mono h n).trans (Ideal.le_comap_pow f n)

def adicMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) f (pow_le_comap_pow h n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun {m n} hle => by
      ext x
      induction x using AdicCompletion.induction_on with
      | h x =>
        simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
          Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
        rw [← Ideal.quotientMap_mk (H := pow_le_comap_pow h m),
          ← Ideal.quotientMap_mk (H := pow_le_comap_pow h m), AdicCompletion.Ideal.mk_eq_mk I hle])

theorem evalₐ_adicMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f) (n : ℕ)
    (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (adicMap I J f h x) =
      Ideal.quotientMap (J ^ n) f (pow_le_comap_pow h n) (AdicCompletion.evalₐ I n x) := by
  unfold adicMap
  rw [AdicCompletion.evalₐ_liftRingHom]
  · rfl
  · intro m n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h x =>
      simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk,
        Ideal.quotientMap_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      rw [← Ideal.quotientMap_mk (H := pow_le_comap_pow h m),
        ← Ideal.quotientMap_mk (H := pow_le_comap_pow h m), AdicCompletion.Ideal.mk_eq_mk I hle]

@[simp] theorem adicMap_algebraMap (I : Ideal A) (J : Ideal B) (f : A →+* B) (h : I ≤ J.comap f)
    (a : A) : adicMap I J f h (algebraMap A _ a) = algebraMap B _ (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap, AlgHom.commutes, AlgHom.commutes]
  rfl

theorem adicMap_eq_id (I : Ideal A) (f : A →+* A) (h : I ≤ I.comap f) (hf : ∀ a, f a = a)
    (x : AdicCompletion I A) : adicMap I I f h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, hf]

theorem adicMap_adicMap (I : Ideal A) (J : Ideal B) (K : Ideal C) (f : A →+* B) (g : B →+* C)
    (e : A →+* C) (h : I ≤ J.comap f) (h' : J ≤ K.comap g) (h'' : I ≤ K.comap e)
    (he : ∀ a, g (f a) = e a) (x : AdicCompletion I A) :
    adicMap J K g h' (adicMap I J f h x) = adicMap I K e h'' x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap, evalₐ_adicMap, evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, he]

theorem span_natCast_le_comap (p : ℕ) (f : A →+* B) :
    span {(p : A)} ≤ (span {(p : B)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simp [Ideal.mem_comap]

end Adic

variable (p : ℕ) [Fact p.Prime]
variable (R : Type u) [CommRing R] [Fact ¬IsUnit (p : R)]
variable (S : Type v) [CommRing S] [Fact ¬IsUnit (p : S)]
variable (U : Type w) [CommRing U] [Fact ¬IsUnit (p : U)]

abbrev Tilt : Type u := PreTilt R p

abbrev Ainf : Type u := WittVector p (Tilt p R)

abbrev AinfInv : Type u := Localization.Away (p : Ainf p R)

variable {R S U}

namespace Tilt

def map (f : R →+* S) : Tilt p R →+* Tilt p S :=
  Perfection.map p (Ideal.quotientMap (span {(p : S)}) f (span_natCast_le_comap p f))

variable {p}

theorem ext {x y : Tilt p R} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) : x = y :=
  Perfection.ext h

theorem coeff_map (f : R →+* S) (x : Tilt p R) (n : ℕ) :
    PreTilt.coeff n (map p f x) =
      Ideal.quotientMap (span {(p : S)}) f (span_natCast_le_comap p f) (PreTilt.coeff n x) := rfl

@[simp] theorem map_id (x : Tilt p R) : map p (RingHom.id R) x = x := by
  refine ext fun n => ?_
  rw [coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [← ha]; rfl

theorem map_map (f : R →+* S) (g : S →+* U) (x : Tilt p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  refine ext fun n => ?_
  rw [coeff_map, coeff_map, coeff_map]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  rw [← ha]; rfl

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

theorem untilt_map (f : R →+* S) (x : Tilt p R) :
    PreTilt.untilt (map p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  refine ⟨f a, ?_, ?_⟩
  · change _ = PreTilt.coeff n (map p f x)
    rw [coeff_map, ← ha]; rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := a)
      (n := n) ha
    rw [SModEq.sub_mem] at h ⊢
    have h2 := pow_le_comap_pow (span_natCast_le_comap p f) (n + 1) (neg_mem h)
    rw [Ideal.mem_comap, neg_sub, map_sub, map_pow] at h2
    exact h2

end Tilt

namespace Ainf

abbrev teich : Tilt p R →* Ainf p R := WittVector.teichmuller p

variable (R) in

def frob : Ainf p R →+* Ainf p R := WittVector.frobenius

def map (f : R →+* S) : Ainf p R →+* Ainf p S := WittVector.map (Tilt.map p f)

variable (R) in

def ofPadicInt : ℤ_[p] →+* Ainf p R :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (Tilt p R))).comp (WittVector.equiv p).symm.toRingHom

instance : Algebra ℤ_[p] (Ainf p R) := (ofPadicInt p R).toAlgebra

variable {p}

@[simp] theorem map_id (x : Ainf p R) : map p (RingHom.id R) x = x := by
  ext n; simp [map]

theorem map_map (f : R →+* S) (g : S →+* U) (x : Ainf p R) :
    map p g (map p f x) = map p (g.comp f) x := by
  ext n; simp [map, Tilt.map_map]

@[simp] theorem map_teich (f : R →+* S) (x : Tilt p R) :
    map p f (teich p x) = teich p (Tilt.map p f x) := WittVector.map_teichmuller p _ x

theorem frob_eq_map : frob p R = WittVector.map (frobenius (Tilt p R) p) :=
  WittVector.frobenius_eq_map_frobenius p

@[simp] theorem frob_teich (x : Tilt p R) : frob p R (teich p x) = teich p x ^ p := by
  rw [frob_eq_map, ← map_pow]; exact WittVector.map_teichmuller p _ x

theorem map_frob (f : R →+* S) (x : Ainf p R) : map p f (frob p R x) = frob p S (map p f x) := by
  ext n; simp [map, frob_eq_map, frobenius_def]

theorem frob_bijective : Function.Bijective (frob p R) := WittVector.frobenius_bijective p _

@[simp] theorem map_algebraMap (f : R →+* S) (a : ℤ_[p]) :
    map p f (algebraMap ℤ_[p] _ a) = algebraMap ℤ_[p] _ a := by
  ext n
  change Tilt.map p f (ZMod.castHom (dvd_refl p) (Tilt p R) _) = ZMod.castHom (dvd_refl p) _ _
  exact RingHom.congr_fun (Subsingleton.elim ((Tilt.map p f).comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) (Tilt p S))) _

@[simp] theorem frob_algebraMap (a : ℤ_[p]) :
    frob p R (algebraMap ℤ_[p] _ a) = algebraMap ℤ_[p] _ a := by
  rw [frob_eq_map]
  ext n
  change frobenius _ p (ZMod.castHom (dvd_refl p) (Tilt p R) _) = ZMod.castHom (dvd_refl p) _ _
  exact RingHom.congr_fun (Subsingleton.elim ((frobenius _ p).comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) (Tilt p R))) _

theorem p_dvd_frob_sub_pow (x : Ainf p R) : (p : Ainf p R) ∣ frob p R x - x ^ p := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
    frob_eq_map]
  simp [frobenius_def]

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

variable (p R) in

def theta : Ainf p R →+* R := WittVector.fontaineTheta R p

@[simp] theorem theta_teich (x : Tilt p R) : theta p R (teich p x) = PreTilt.untilt x :=
  WittVector.fontaineTheta_teichmuller x

theorem theta_map (f : R →+* S) (x : Ainf p R) : theta p S (map p f x) = f (theta p R x) := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : S)})]
  intro n
  rw [smul_eq_mul, Ideal.mul_top, SModEq]
  have := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp ((theta p S).comp (map p f)))
    ((Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (theta p R)))
    (by
      refine ⟨n, ?_⟩
      rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (mem_span_singleton_self _) _)
    (by intro y; simp [Tilt.untilt_map])
  exact RingHom.congr_fun this x

end Ainf

namespace AinfInv

theorem isUnit_p : IsUnit (p : AinfInv p R) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (S := AinfInv p R) (p : Ainf p R)

def extend (f : Ainf p R →+* Ainf p S) : AinfInv p R →+* AinfInv p S :=
  IsLocalization.Away.lift (p : Ainf p R) (g := (algebraMap (Ainf p S) (AinfInv p S)).comp f)
    (by simpa using isUnit_p p)

variable {p} in
@[simp] theorem extend_algebraMap (f : Ainf p R →+* Ainf p S) (x : Ainf p R) :
    extend p f (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  IsLocalization.Away.lift_eq _ _ x

variable {p} in
theorem hom_ext {B : Type*} [CommRing B] {f g : AinfInv p R →+* B}
    (h : ∀ x : Ainf p R, f (algebraMap _ _ x) = g (algebraMap _ _ x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : Ainf p R)) (RingHom.ext h)

variable (R) in

def frob : AinfInv p R →+* AinfInv p R := extend p (Ainf.frob p R)

def map (f : R →+* S) : AinfInv p R →+* AinfInv p S := extend p (Ainf.map p f)

end AinfInv

def padicLift {B : Type*} [CommRing B] (f : ℤ_[p] →+* B) (h : IsUnit (p : B)) : ℚ_[p] →+* B :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (g := f) (by
    rintro ⟨x, hx⟩
    have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
    change IsUnit (f x)
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast]
    exact ((Units.isUnit _).map f).mul (h.pow _))

@[simp] theorem padicLift_algebraMap {B : Type*} [CommRing B] (f : ℤ_[p] →+* B)
    (h : IsUnit (p : B)) (a : ℤ_[p]) : padicLift p f h (algebraMap _ _ a) = f a :=
  IsLocalization.lift_eq _ a

variable {p} in
theorem padic_hom_ext {B : Type*} [CommRing B] {f g : ℚ_[p] →+* B}
    (h : ∀ a : ℤ_[p], f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext h)

namespace AinfInv

instance : Algebra ℚ_[p] (AinfInv p R) :=
  (padicLift p (algebraMap ℤ_[p] (AinfInv p R)) (isUnit_p p)).toAlgebra

instance : Algebra ℚ (AinfInv p R) :=
  ((algebraMap ℚ_[p] (AinfInv p R)).comp (algebraMap ℚ ℚ_[p])).toAlgebra

instance : IsScalarTower ℤ_[p] ℚ_[p] (AinfInv p R) :=
  IsScalarTower.of_algebraMap_eq fun a => (padicLift_algebraMap p _ _ a).symm

variable {p}

@[simp] theorem map_algebraMap (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := extend_algebraMap _ x

@[simp] theorem frob_algebraMap (x : Ainf p R) :
    frob p R (algebraMap _ _ x) = algebraMap _ _ (Ainf.frob p R x) := extend_algebraMap _ x

@[simp] theorem map_id (x : AinfInv p R) : map p (RingHom.id R) x = x :=
  RingHom.congr_fun (hom_ext (f := map p (RingHom.id R)) (g := RingHom.id _) (by simp)) x

theorem map_map (f : R →+* S) (g : S →+* U) (x : AinfInv p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  RingHom.congr_fun (hom_ext (f := (map p g).comp (map p f)) (g := map p (g.comp f))
    (by simp [Ainf.map_map])) x

theorem map_frob (f : R →+* S) (x : AinfInv p R) : map p f (frob p R x) = frob p S (map p f x) :=
  RingHom.congr_fun (hom_ext (f := (map p f).comp (frob p R)) (g := (frob p S).comp (map p f))
    (by simp [Ainf.map_frob])) x

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

variable (p R) in

def theta : AinfInv p R →+* Localization.Away (p : R) := fontaineThetaInvertP R p

@[simp] theorem theta_algebraMap (x : Ainf p R) :
    theta p R (algebraMap _ _ x) = algebraMap R _ (Ainf.theta p R x) := by
  unfold theta fontaineThetaInvertP Localization.awayLift
  rw [IsLocalization.Away.lift_eq]
  rfl

end AinfInv

def awayMap {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    Localization.Away (p : R) →+* Localization.Away (p : S) :=
  IsLocalization.Away.lift (p : R) (g := (algebraMap S (Localization.Away (p : S))).comp f)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : S)) (p : S))

omit [Fact p.Prime] in
@[simp] theorem awayMap_algebraMap {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) : awayMap p f (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  IsLocalization.Away.lift_eq _ _ x

variable {p} in
theorem AinfInv.theta_map [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]
    (f : R →+* S) (x : AinfInv p R) :
    AinfInv.theta p S (AinfInv.map p f x) = awayMap p f (AinfInv.theta p R x) :=
  RingHom.congr_fun (AinfInv.hom_ext (f := (AinfInv.theta p S).comp (AinfInv.map p f))
    (g := (awayMap p f).comp (AinfInv.theta p R)) (by simp [Ainf.theta_map])) x

end Reformulated.AutPerF
