import Mathlib
import GroundTheory.PAdicHodge.ACrisGalois
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime]

variable (l) in

abbrev Ainf : Type := AInf ℂ_[l] l

variable (l) in

abbrev Acris : Type := ACris.ACris ℂ_[l] l

variable (l) in

abbrev Acris0 : Type := ↥(ACris.ACrisZero ℂ_[l] l)

variable (l) in

abbrev theta0 : Ainf l →+* OC l := WittVector.fontaineTheta (OC l) l

theorem ker_theta0 : RingHom.ker (theta0 l) = Ideal.span {xi0 l} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller untilt_pFlat

variable (l) in

abbrev WL (R : Type) [CommRing R] : Type := Localization.Away (l : WittVector l R)

section Away
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

def awayW (f : R →+* S) : WL l R →+* WL l S :=
  Localization.awayLift ((algebraMap (WittVector l S) (WL l S)).comp (WittVector.map f)) (l : WittVector l R) (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit (l : WittVector l S))

theorem awayW_algebraMap (f : R →+* S) (x : WittVector l R) :
    awayW f (algebraMap _ (WL l R) x) = algebraMap _ (WL l S) (WittVector.map f x) := IsLocalization.lift_eq _ x

theorem awayW_ext {B : Type} [CommRing B] {F G : WL l R →+* B}
    (h : ∀ x : WittVector l R, F (algebraMap _ (WL l R) x) = G (algebraMap _ (WL l R) x)) : F = G :=
  IsLocalization.ringHom_ext (Submonoid.powers (l : WittVector l R)) (RingHom.ext h)

theorem wmap_comp (f : R →+* S) (g : S →+* T) (x : WittVector l R) :
    WittVector.map (g.comp f) x = WittVector.map g (WittVector.map f x) := by
  ext i; simp only [WittVector.map_coeff, RingHom.comp_apply]

theorem wmap_id (x : WittVector l R) : WittVector.map (RingHom.id R) x = x := by
  ext i; simp only [WittVector.map_coeff, RingHom.id_apply]

theorem awayW_comp (f : R →+* S) (g : S →+* T) : awayW (l := l) (g.comp f) = (awayW g).comp (awayW f) :=
  awayW_ext fun x => by rw [RingHom.comp_apply, awayW_algebraMap, awayW_algebraMap, awayW_algebraMap, wmap_comp]

theorem awayW_id : awayW (l := l) (RingHom.id R) = RingHom.id _ :=
  awayW_ext fun x => by rw [awayW_algebraMap, wmap_id]; rfl

def dpw (k : ℕ) (x : WittVector l R) : WL l R :=
  Ring.inverse (k.factorial : WL l R) * algebraMap _ (WL l R) x ^ k

theorem awayW_dpw (f : R →+* S) (k : ℕ) (h : IsUnit (k.factorial : WL l R)) (x : WittVector l R) :
    awayW f (dpw k x) = dpw k (WittVector.map f x) := by
  rw [dpw, dpw, map_mul, map_pow, awayW_algebraMap]
  congr 1
  have h' : IsUnit (k.factorial : WL l S) := by simpa using h.map (awayW f)
  apply h'.mul_left_cancel
  rw [Ring.mul_inverse_cancel _ h', ← map_natCast (awayW f), ← map_mul, Ring.mul_inverse_cancel _ h, map_one]

end Away

namespace PAlg

variable (A B C : PAlg l)

instance : Algebra (Ob l) A.A := A.s.toAlgebra
instance : Algebra (Ainf l) A.W := A.sW.toAlgebra

theorem natCast_l : (l : A.A) = 0 := by
  rw [← map_natCast A.s, CharP.cast_eq_zero, map_zero]

theorem isUnit_natCast {m : ℕ} (hm : m ≠ 0) : IsUnit (m : WL l A.A) := by
  simpa using (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) hm).map (awayW A.s)

def frob : A.A →+* A.A where
  toFun x := x ^ l
  map_one' := one_pow _
  map_mul' x y := mul_pow x y l
  map_zero' := zero_pow (Fact.out : l.Prime).ne_zero
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) x y
    rw [hr, A.natCast_l]; simp

def sharp : A.A →* A.U := A.th.toMonoidHom.comp (WittVector.teichmuller l)

def oC : OC l →+* A.U :=
  (theta0 l).liftOfSurjective (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l) ⟨A.th.comp A.sW, by
    rw [ker_theta0, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩

theorem oC_theta0 (x : Ainf l) : A.oC (theta0 l x) = A.th (A.sW x) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ x

theorem dpw_xi_mem (k : ℕ) : dpw k A.xi ∈ A.Acr0 := Algebra.subset_adjoin ⟨k, rfl⟩

def dxi0 (k : ℕ) : A.Acr0 := ⟨dpw k A.xi, A.dpw_xi_mem k⟩

def mkAcr (n : ℕ) : A.Acr0 →+* A.Acr n := Ideal.Quotient.mk _

def dxi (n k : ℕ) : A.Acr n := A.mkAcr n (A.dxi0 k)

def Fil0 (r : ℕ) : Ideal A.Acr0 := Ideal.span {z | ∃ k, r ≤ k ∧ z = A.dxi0 k}

def Fil (n r : ℕ) : Ideal (A.Acr n) := Ideal.span {z | ∃ k, r ≤ k ∧ z = A.dxi n k}

def PFil (n : ℕ) : Ideal (A.Acr n) := Ideal.span {(l : A.Acr n)} ⊔ A.Fil n 1

theorem pow_l_acr (n : ℕ) : (l : A.Acr n) ^ n = 0 := by
  rw [← map_natCast (A.mkAcr n), ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

theorem toAcr_xi (n : ℕ) : A.toAcr n A.xi = A.dxi n 1 :=
  congrArg (A.mkAcr n) (Subtype.ext (by simp [dxi0, dpw]))

def uToQ (n : ℕ) : A.U →+* A.Acr n ⧸ A.Fil n 1 :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (A.toAcr n)) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [RingHom.comp_apply, map_mul, toAcr_xi]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩))

theorem uToQ_th (n : ℕ) (x : A.W) : A.uToQ n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := rfl

def uToPQ (n : ℕ) : A.U →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.factor le_sup_right).comp (A.uToQ n)

def red {m n : ℕ} (h : n ≤ m) : A.Acr m →+* A.Acr n :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h))

theorem red_mk {m n : ℕ} (h : n ≤ m) (x : A.Acr0) : A.red h (A.mkAcr m x) = A.mkAcr n x := rfl

theorem awayW_s_mem {y : WL l (Ob l)} (hy : y ∈ ACris.ACrisZero ℂ_[l] l) : awayW A.s y ∈ A.Acr0 := by
  rw [ACris.acrisZero_eq_adjoin ker_theta0] at hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have := awayW_dpw A.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero) (xi0 l)
    exact this ▸ A.dpw_xi_mem k
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def cris0 : Acris0 l →+* A.Acr0 :=
  ((awayW A.s).comp (ACris.ACrisZero ℂ_[l] l).val.toRingHom).codRestrict A.Acr0 fun y => A.awayW_s_mem y.2

instance hausdorffAcr (n : ℕ) : IsHausdorff (Ideal.span {(l : A.Acr n)}) (A.Acr n) :=
  ⟨fun x hx => by
    have := hx n
    rw [Ideal.span_singleton_pow, pow_l_acr, Ideal.span_singleton_zero, Submodule.bot_smul, SModEq.bot] at this
    exact this⟩

def cris (n : ℕ) : Acris l →+* A.Acr n :=
  (Ideal.Quotient.lift _ ((A.mkAcr n).comp A.cris0) fun a ha => by
    rw [Ideal.span_singleton_pow] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, pow_l_acr, mul_zero]).comp
    (AdicCompletion.evalₐ (Ideal.span {(l : Acris0 l)}) n).toRingHom

theorem cris_of (n : ℕ) (y : Acris0 l) : A.cris n (AdicCompletion.of _ _ y) = A.mkAcr n (A.cris0 y) := by
  simp only [cris, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AdicCompletion.evalₐ_of,
    Ideal.Quotient.lift_mk]

theorem cris_algebraMap (n : ℕ) (x : Ainf l) : A.cris n (algebraMap (Ainf l) (Acris l) x) = A.toAcr n (A.sW x) := by
  rw [AdicCompletion.algebraMap_apply, cris_of]
  exact congrArg (A.mkAcr n) (Subtype.ext (awayW_algebraMap A.s x))

instance (n : ℕ) : Algebra (Acris l) (A.Acr n) := (A.cris n).toAlgebra
instance (n : ℕ) : Algebra A.W (A.Acr n) := (A.toAcr n).toAlgebra
instance (n : ℕ) : Algebra (Ainf l) (A.Acr n) := ((A.toAcr n).comp A.sW).toAlgebra
instance (n : ℕ) : IsScalarTower (Ainf l) (Acris l) (A.Acr n) :=
  IsScalarTower.of_algebraMap_eq fun x => (A.cris_algebraMap n x).symm
instance (n : ℕ) : IsScalarTower (Ainf l) A.W (A.Acr n) := IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev Wn (n : ℕ) : Type := A.W ⧸ Ideal.span {(l : A.W) ^ n}

def wnToAcr (n : ℕ) : A.Wn n →+* A.Acr n :=
  Ideal.Quotient.lift _ (A.toAcr n) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, pow_l_acr, mul_zero]

abbrev Un (n : ℕ) : Type := A.U ⧸ Ideal.span {(l : A.U) ^ n}

instance : Algebra (Ainf l) A.U := (A.th.comp A.sW).toAlgebra

abbrev Q (a : Ob l) : Type := A.A ⧸ Ideal.span {A.s a}

variable {A B C}

def PdOk (f : A.A →+* B.A) : Prop := ∀ k, dpw k (WittVector.map f A.xi) ∈ B.Acr0

theorem PdOk.mem {f : A.A →+* B.A} (h : PdOk f) {y : WL l A.A} (hy : y ∈ A.Acr0) : awayW f y ∈ B.Acr0 := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    have := awayW_dpw f k (A.isUnit_natCast k.factorial_ne_zero) A.xi
    exact this ▸ h k
  | algebraMap x => rw [awayW_algebraMap]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def PdOk.acr0 {f : A.A →+* B.A} (h : PdOk f) : A.Acr0 →+* B.Acr0 :=
  ((awayW f).comp A.Acr0.val.toRingHom).codRestrict B.Acr0 fun y => h.mem y.2

def PdOk.acr {f : A.A →+* B.A} (h : PdOk f) (n : ℕ) : A.Acr n →+* B.Acr n :=
  Ideal.Quotient.lift _ ((B.mkAcr n).comp h.acr0) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, pow_l_acr, mul_zero]

theorem PdOk.acr_mk {f : A.A →+* B.A} (h : PdOk f) (n : ℕ) (y : A.Acr0) :
    h.acr n (A.mkAcr n y) = B.mkAcr n (h.acr0 y) := rfl

theorem PdOk.acr_toAcr {f : A.A →+* B.A} (h : PdOk f) (n : ℕ) (x : A.W) :
    h.acr n (A.toAcr n x) = B.toAcr n (WittVector.map f x) :=
  congrArg (B.mkAcr n) (Subtype.ext (awayW_algebraMap f x))

theorem PdOk.acr_comp {f : A.A →+* B.A} {g : B.A →+* C.A} (h : PdOk f) (h' : PdOk g) (h'' : PdOk (g.comp f)) (n : ℕ)
    (x : A.Acr n) : h''.acr n x = h'.acr n (h.acr n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (C.mkAcr n) (Subtype.ext (RingHom.congr_fun (awayW_comp f g) y.1))

theorem PdOk.acr_id (h : PdOk (RingHom.id A.A)) (n : ℕ) (x : A.Acr n) : h.acr n x = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (A.mkAcr n) (Subtype.ext (RingHom.congr_fun awayW_id y.1))

theorem PdOk.red_acr {f : A.A →+* B.A} (h : PdOk f) {m n : ℕ} (e : n ≤ m) (x : A.Acr m) :
    B.red e (h.acr m x) = h.acr n (A.red e x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem pdOk_of_over {f : A.A →+* B.A} {τ : Ob l →+* Ob l} (hf : f.comp A.s = B.s.comp τ)
    (hτ : ∀ k, ACris.dpow k (WittVector.map τ (xi0 l)) ∈ ACris.ACrisZero ℂ_[l] l) : PdOk f := fun k => by
  have e : WittVector.map f A.xi = WittVector.map B.s (WittVector.map τ (xi0 l)) := by
    rw [← wmap_comp, ← hf, wmap_comp]; rfl
  rw [e, ← awayW_dpw B.s k (ACris.isUnit_natCast (K := ℂ_[l]) (p := l) k.factorial_ne_zero)]
  exact B.awayW_s_mem (hτ k)

theorem PdOk.acr_cris {f : A.A →+* B.A} (h : PdOk f) {τ : Ob l →+* Ob l} (hf : f.comp A.s = B.s.comp τ)
    (g : Acris0 l →+* Acris0 l) (hg : ∀ y : Acris0 l, (g y).1 = awayW τ y.1) (n : ℕ) (a : Acris l) :
    h.acr n (A.cris n a) = B.cris n (ACris.extendEndo g a) := by
  refine RingHom.congr_fun (ACris.ringHom_ext (F := (h.acr n).comp (A.cris n))
    (G := (B.cris n).comp (ACris.extendEndo g)) fun y => ?_) a
  rw [RingHom.comp_apply, RingHom.comp_apply, ACris.extendEndo_of, cris_of, cris_of, acr_mk]
  refine congrArg (B.mkAcr n) (Subtype.ext ?_)
  change awayW f (awayW A.s y.1) = awayW B.s (g y).1
  rw [hg, ← RingHom.comp_apply, ← awayW_comp, hf, awayW_comp]; rfl

theorem xi0_mem : xi0 l ∈ RingHom.ker (theta0 l) := by
  rw [ker_theta0]; exact Ideal.mem_span_singleton_self _

theorem pdOk_hom (f : A ⟶ B) : PdOk (Hom.f f) := fun k => by
  have := mapW_xi f
  rw [mapW] at this
  rw [this]; exact B.dpw_xi_mem k

def mapAcr (f : A ⟶ B) (n : ℕ) : A.Acr n →+* B.Acr n := (pdOk_hom f).acr n

theorem mapAcr_cris (f : A ⟶ B) (n : ℕ) (a : Acris l) : mapAcr f n (A.cris n a) = B.cris n a := by
  have := (pdOk_hom f).acr_cris (τ := RingHom.id _) (Hom.comm f) (RingHom.id _) (fun y => by rw [awayW_id]; rfl) n a
  rwa [ACris.extendEndo_id] at this

theorem mapAcr_toAcr (f : A ⟶ B) (n : ℕ) (x : A.W) : mapAcr f n (A.toAcr n x) = B.toAcr n (mapW f x) :=
  (pdOk_hom f).acr_toAcr n x

theorem mapAcr_id (n : ℕ) (x : A.Acr n) : mapAcr (𝟙 A) n x = x := PdOk.acr_id _ n x

theorem mapAcr_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) (x : A.Acr n) : mapAcr (f ≫ g) n x = mapAcr g n (mapAcr f n x) :=
  PdOk.acr_comp _ _ _ n x

theorem mapAcr_dxi (f : A ⟶ B) (n k : ℕ) : mapAcr f n (A.dxi n k) = B.dxi n k := by
  refine congrArg (B.mkAcr n) (Subtype.ext ?_)
  have := awayW_dpw (Hom.f f) k (A.isUnit_natCast k.factorial_ne_zero) A.xi
  exact this.trans (congrArg (dpw k) (mapW_xi f))

theorem mapAcr_fil (f : A ⟶ B) (n r : ℕ) : A.Fil n r ≤ (B.Fil n r).comap (mapAcr f n) := by
  rw [Fil, Ideal.span_le]
  rintro _ ⟨k, hk, rfl⟩
  exact Ideal.subset_span ⟨k, hk, mapAcr_dxi f n k⟩

def mapAcrₐ (f : A ⟶ B) (n : ℕ) : A.Acr n →ₐ[Acris l] B.Acr n := ⟨mapAcr f n, mapAcr_cris f n⟩

theorem mapU_th (f : A ⟶ B) (x : A.W) : mapU f (A.th x) = B.th (mapW f x) := rfl

theorem mapW_sW (f : A ⟶ B) (x : Ainf l) : mapW f (A.sW x) = B.sW x := by
  rw [mapW, sW, sW, ← wmap_comp, Hom.comm f]

theorem mapU_oC (f : A ⟶ B) (x : OC l) : mapU f (A.oC x) = B.oC x := by
  obtain ⟨y, rfl⟩ := IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l x
  rw [oC_theta0, oC_theta0, mapU_th, mapW_sW]

theorem mapU_id : mapU (𝟙 A) = RingHom.id _ := Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg A.th (wmap_id x))

theorem mapU_comp (f : A ⟶ B) (g : B ⟶ C) : mapU (f ≫ g) = (mapU g).comp (mapU f) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun x => congrArg C.th (wmap_comp (Hom.f f) (Hom.f g) x))

def mapUg (f : A ⟶ B) : A.Ug →+* B.Ug :=
  Localization.awayLift ((algebraMap B.U B.Ug).comp (mapU f)) (l : A.U) (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit (l : B.U))

theorem mapUg_algebraMap (f : A ⟶ B) (x : A.U) : mapUg f (algebraMap _ _ x) = algebraMap _ _ (mapU f x) :=
  IsLocalization.lift_eq _ x

def wnMap (f : A.A →+* B.A) (n : ℕ) : A.Wn n →+* B.Wn n :=
  Ideal.quotientMap _ (WittVector.map f) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _)

def mapUn (f : A ⟶ B) (n : ℕ) : A.Un n →+* B.Un n :=
  Ideal.quotientMap _ (mapU f) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _)

def mapQ (f : A ⟶ B) (a : Ob l) : A.Q a →+* B.Q a :=
  Ideal.quotientMap _ (Hom.f f) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, ← RingHom.comp_apply, Hom.comm f]
    exact Ideal.mem_span_singleton_self _)

section Phi
variable (A)

theorem wmap_frobenius (x : Ainf l) : WittVector.map (frobenius (Ob l) l) x = WittVector.frobeniusEquiv l (Ob l) x := by
  ext i; rw [WittVector.frobeniusEquiv_coeff, WittVector.map_coeff, frobenius_def]

theorem frob_comp_s : A.frob.comp A.s = A.s.comp (frobenius (Ob l) l) := RingHom.ext fun x => (map_pow A.s x l).symm

theorem pdOk_frob : PdOk A.frob :=
  pdOk_of_over A.frob_comp_s fun k => by rw [wmap_frobenius]; exact ACris.dpow_frobenius_mem xi0_mem k

def phiW : A.W →+* A.W := WittVector.map A.frob

def phi (n : ℕ) : A.Acr n →+* A.Acr n := A.pdOk_frob.acr n

theorem phi_cris (n : ℕ) (a : Acris l) : A.phi n (A.cris n a) = A.cris n (ACris.phi ℂ_[l] l a) :=
  A.pdOk_frob.acr_cris A.frob_comp_s (ACris.phiZero ℂ_[l] l) (fun y => RingHom.congr_fun (f := ACris.phiAway ℂ_[l] l)
    (awayW_ext fun x => by rw [ACris.phiAway_algebraMap, awayW_algebraMap, wmap_frobenius]) y.1) n a

theorem phi_toAcr (n : ℕ) (x : A.W) : A.phi n (A.toAcr n x) = A.toAcr n (A.phiW x) := A.pdOk_frob.acr_toAcr n x

variable {A}

theorem mapAcr_phi (f : A ⟶ B) (n : ℕ) (x : A.Acr n) : mapAcr f n (A.phi n x) = B.phi n (mapAcr f n x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine congrArg (B.mkAcr n) (Subtype.ext ?_)
  change awayW (Hom.f f) (awayW A.frob y.1) = awayW B.frob (awayW (Hom.f f) y.1)
  rw [← RingHom.comp_apply, ← awayW_comp, ← RingHom.comp_apply, ← awayW_comp]
  congr 2
  exact RingHom.ext fun x => map_pow (Hom.f f) x l

variable (A) in

def Fix (n : ℕ) : Subring (A.Wn n) := RingHom.eqLocus (wnMap A.frob n) (RingHom.id _)

def mapFix (f : A ⟶ B) (n : ℕ) : A.Fix n →+* B.Fix n :=
  ((wnMap (Hom.f f) n).comp (A.Fix n).subtype).codRestrict _ fun x => by
    obtain ⟨x, hx⟩ := x
    change wnMap B.frob n (wnMap (Hom.f f) n x) = wnMap (Hom.f f) n x
    have hx' : wnMap A.frob n x = x := hx
    conv_rhs => rw [← hx']
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (WittVector.map _ (WittVector.map _ y)) = Ideal.Quotient.mk _ (WittVector.map _ (WittVector.map _ y))
    rw [← wmap_comp, ← wmap_comp]
    congr 3
    exact RingHom.ext fun x => (map_pow (Hom.f f) x l).symm

variable (A) in

def fixToAcr (n : ℕ) : A.Fix n →+* A.Acr n := (A.wnToAcr n).comp (A.Fix n).subtype

end Phi

end PAlg

open PAlg

variable (l)

def AcrA (n : ℕ) : PAlg l ⥤ CommAlgCat.{0} (Acris l) where
  obj A := CommAlgCat.of _ (A.Acr n)
  map f := CommAlgCat.ofHom (mapAcrₐ f n)
  map_id A := CommAlgCat.hom_ext (AlgHom.ext fun x => mapAcr_id n x)
  map_comp f g := CommAlgCat.hom_ext (AlgHom.ext fun x => mapAcr_comp f g n x)

abbrev AcrF (n : ℕ) : PAlg l ⥤ ModuleCat.{0} (Acris l) := CH.modF (AcrA l n)

def FilS (n r : ℕ) : CH.SubF (AcrF l n) where
  S A := (A.Fil n r).restrictScalars (Acris l)
  map_mem f _ hx := mapAcr_fil f n r hx

abbrev FilF (n r : ℕ) : PAlg l ⥤ ModuleCat.{0} (Acris l) := (FilS l n r).fn

def redF {m n : ℕ} (h : n ≤ m) : AcrF l m ⟶ AcrF l n where
  app A := ModuleCat.ofHom (AlgHom.toLinearMap (R := Acris l) ⟨A.red h, fun a =>
    RingHom.congr_fun (ACris.ringHom_ext (F := (A.red h).comp (A.cris m)) (G := A.cris n) fun y => by
      rw [RingHom.comp_apply, cris_of, cris_of, red_mk]) a⟩)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext fun x => (pdOk_hom f).red_acr h x)

def WnF (n : ℕ) : PAlg l ⥤ ModuleCat.{0} (Ainf l) where
  obj A := ModuleCat.of _ (A.Wn n)
  map {A B} f := ModuleCat.ofHom (AlgHom.toLinearMap (R := Ainf l) ⟨wnMap (Hom.f f) n, fun a =>
    congrArg (Ideal.Quotient.mk _) (mapW_sW f a)⟩)
  map_id A := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (wmap_id y))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (wmap_comp (Hom.f f) (Hom.f g) y))

def UnF (n : ℕ) : PAlg l ⥤ ModuleCat.{0} (Ainf l) where
  obj A := ModuleCat.of _ (A.Un n)
  map {A B} f := ModuleCat.ofHom (AlgHom.toLinearMap (R := Ainf l) ⟨mapUn f n, fun a =>
    congrArg (fun x => Ideal.Quotient.mk _ (B.th x)) (mapW_sW f a)⟩)
  map_id A := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun mapU_id y))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (mapU_comp f g) y))

variable {l} in

def QF (a : Ob l) : PAlg l ⥤ ModuleCat.{0} (Ob l) where
  obj A := ModuleCat.of _ (A.Q a)
  map {A B} f := ModuleCat.ofHom (AlgHom.toLinearMap (R := Ob l) ⟨mapQ f a, fun c =>
    congrArg (Ideal.Quotient.mk _) (RingHom.congr_fun (Hom.comm f) c)⟩)
  map_id A := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl)

def FixR (n : ℕ) : PAlg l ⥤ CommRingCat.{0} where
  obj A := CommRingCat.of (A.Fix n)
  map f := CommRingCat.ofHom (mapFix f n)
  map_id A := CommRingCat.hom_ext (RingHom.ext fun ⟨x, _⟩ => Subtype.ext (by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (wmap_id y)))
  map_comp f g := CommRingCat.hom_ext (RingHom.ext fun ⟨x, _⟩ => Subtype.ext (by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (Ideal.Quotient.mk _) (wmap_comp (Hom.f f) (Hom.f g) y)))

def UR : PAlg l ⥤ CommRingCat.{0} where
  obj A := CommRingCat.of A.U
  map f := CommRingCat.ofHom (mapU f)
  map_id _ := CommRingCat.hom_ext mapU_id
  map_comp f g := CommRingCat.hom_ext (mapU_comp f g)

def UgR : PAlg l ⥤ CommRingCat.{0} where
  obj A := CommRingCat.of A.Ug
  map f := CommRingCat.ofHom (mapUg f)
  map_id A := CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers (l : A.U)) (RingHom.ext fun x =>
    (mapUg_algebraMap (𝟙 A) x).trans (by rw [mapU_id]; rfl)))
  map_comp {A B C} f g := CommRingCat.hom_ext (IsLocalization.ringHom_ext (Submonoid.powers (l : A.U)) (RingHom.ext fun x =>
    (mapUg_algebraMap (f ≫ g) x).trans (by
      change _ = mapUg g (mapUg f (algebraMap _ _ x))
      rw [mapUg_algebraMap, mapUg_algebraMap, mapU_comp]; rfl)))

abbrev testι : Test l ⥤ PAlg l := ObjectProperty.ι _

end CrystallineSemistableComparison
