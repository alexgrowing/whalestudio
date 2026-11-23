import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
import GroundTheory.PAdicHodge.BCrisPlusInvariants

noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem away_exists {A E : Type} [CommRing A] [CommRing E] {a : A} (F : Localization.Away a →+* E)
    (f : A →+* E) (h : ∀ x, F (algebraMap A (Localization.Away a) x) = f x)
    (y : Localization.Away a) : ∃ (k : ℕ) (x : A), f x = f a ^ k * F y := by
  obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers a) y
  refine ⟨k, x, ?_⟩
  have h1 := congrArg F e
  rw [map_mul, h, h, map_pow] at h1
  rw [← h1, mul_comm]

variable {A : Type} [CommRing A] {a t : A}

theorem loc2_surj (x : Per6.Loc2 a t) : ∃ (m n : ℕ) (y : A),
    Per6.Loc2.mk₀ a t a ^ m * Per6.Loc2.mk₀ a t t ^ n * x = Per6.Loc2.mk₀ a t y := by
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj
    (S := Localization.Away (algebraMap A (Localization.Away a) t))
    (Submonoid.powers (algebraMap A (Localization.Away a) t)) x
  obtain ⟨⟨y, ⟨_, m, rfl⟩⟩, hy⟩ := IsLocalization.surj (S := Localization.Away a)
    (Submonoid.powers a) z
  refine ⟨m, n, y, ?_⟩
  have h1 : x * Per6.Loc2.mk₁ a t (algebraMap A (Localization.Away a) t ^ n) =
      Per6.Loc2.mk₁ a t z := hz
  have h2 := congrArg (Per6.Loc2.mk₁ a t) hy
  simp only [map_mul, map_pow] at h1 h2
  have e : ∀ w, Per6.Loc2.mk₀ a t w = Per6.Loc2.mk₁ a t (algebraMap A (Localization.Away a) w) :=
    fun _ => rfl
  rw [e, e, e, ← h2, ← h1]
  ring

theorem loc2_lift_injective {E : Type} [CommRing E] (f : A →+* E) (ha : IsUnit (f a))
    (ht : IsUnit (f t)) (hf : Function.Injective f) :
    Function.Injective (Per6.Loc2.lift f ha ht) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, n, y, h⟩ := loc2_surj x
  have h1 := congrArg (Per6.Loc2.lift f ha ht) h
  rw [map_mul, hx, mul_zero, Per6.Loc2.lift_mk₀] at h1
  have hy : y = 0 := hf (h1.symm.trans (map_zero f).symm)
  rw [hy, map_zero] at h
  exact (((Per6.Loc2.isUnit_left a t).pow m).mul
    ((Per6.Loc2.isUnit_right a t).pow n)).mul_right_eq_zero.1 h

def IsFrac {B : Type} [CommRing B] (f : A →+* B) (a t : A) : Prop :=
  IsUnit (f a) ∧ IsUnit (f t) ∧ ∀ x : B, ∃ (m n : ℕ) (y : A), f a ^ m * f t ^ n * x = f y

theorem loc2_isFrac : IsFrac (Per6.Loc2.mk₀ a t) a t :=
  ⟨Per6.Loc2.isUnit_left a t, Per6.Loc2.isUnit_right a t, loc2_surj⟩

theorem IsFrac.hom_ext {B E : Type} [CommRing B] [Semiring E] {f : A →+* B} (hf : IsFrac f a t)
    {g h : B →+* E} (e : ∀ x, g (f x) = h (f x)) : g = h := by
  refine RingHom.ext fun x => ?_
  obtain ⟨m, n, y, hy⟩ := hf.2.2 x
  have h1 := congrArg g hy
  have h2 := congrArg h hy
  simp only [map_mul, map_pow] at h1 h2
  rw [← e, ← e, ← e, ← h1] at h2
  exact (((hf.1.map g).pow m).mul ((hf.2.1.map g).pow n)).mul_left_cancel h2.symm

def liftF {E : Type} [Field E] (f : A →+* E) (ha : f a ≠ 0) (ht : f t ≠ 0) : Per6.Loc2 a t →+* E :=
  Per6.Loc2.lift f (isUnit_iff_ne_zero.2 ha) (isUnit_iff_ne_zero.2 ht)

theorem liftF_comp {E : Type} [Field E] (f : A →+* E) (ha : f a ≠ 0) (ht : f t ≠ 0) :
    (liftF f ha ht).comp (Per6.Loc2.mk₀ a t) = f :=
  RingHom.ext (Per6.Loc2.lift_mk₀ f (isUnit_iff_ne_zero.2 ha) (isUnit_iff_ne_zero.2 ht))

theorem loc2_map_comp (f : A →+* A) (ha : f a = a) (c : A) (hc : IsUnit (Per6.Loc2.mk₀ a t c))
    (ht : f t = c * t) :
    (Per6.Loc2.map f ha c hc ht).comp (Per6.Loc2.mk₀ a t) = (Per6.Loc2.mk₀ a t).comp f :=
  RingHom.ext (Per6.Loc2.map_mk₀ f ha c hc ht)

def Fac {B E : Type} [CommRing B] [Field E] (F : B →+* E) (f : A →+* B) (g : A →+* E) : Prop :=
  ∀ x, F (f x) = g x

theorem liftF_fac {E : Type} [Field E] (f : A →+* E) (ha : f a ≠ 0) (ht : f t ≠ 0) :
    Fac (liftF f ha ht) (Per6.Loc2.mk₀ a t) f :=
  RingHom.congr_fun (liftF_comp f ha ht)

def Inj {B E : Type} [CommRing B] [Field E] (f : B →+* E) : Prop := Function.Injective f

theorem liftF_inj {E : Type} [Field E] (f : A →+* E) (ha : f a ≠ 0) (ht : f t ≠ 0)
    (hf : Function.Injective f) : Inj (liftF f ha ht) :=
  loc2_lift_injective f _ _ hf

def pullHom {B C E : Type} [CommRing B] [Field C] [Field E] (ι : B →+* E)
    (hι : Function.Injective ι) (f : C →+* E) (hf : ∀ c, ∃ b, ι b = f c) : C →+* B where
  toFun c := (hf c).choose
  map_one' := hι (by rw [(hf _).choose_spec, map_one, map_one])
  map_mul' x y := hι (by
    rw [map_mul ι, (hf _).choose_spec, (hf _).choose_spec, (hf _).choose_spec, map_mul])
  map_zero' := hι (by rw [(hf _).choose_spec, map_zero, map_zero])
  map_add' x y := hι (by
    rw [map_add ι, (hf _).choose_spec, (hf _).choose_spec, (hf _).choose_spec, map_add])

theorem map_pullHom {B C E : Type} [CommRing B] [Field C] [Field E] (ι : B →+* E)
    (hι : Function.Injective ι) (f : C →+* E) (hf : ∀ c, ∃ b, ι b = f c) (c : C) :
    ι (pullHom ι hι f hf c) = f c :=
  (hf c).choose_spec

theorem exists_map_eq_of_pow_mul {B E : Type} [CommRing B] [Field E] (ι : B →+* E) {u b : B}
    (hu : IsUnit u) {k : ℕ} {z : E} (h : ι b = ι u ^ k * z) : ∃ x, ι x = z :=
  ⟨↑(hu.unit⁻¹) ^ k * b, by
    rw [map_mul, h, map_pow, ← mul_assoc, ← mul_pow, ← map_mul, IsUnit.val_inv_mul, map_one, one_pow,
      one_mul]⟩

end Abstract

variable (l : ℕ) [Fact l.Prime]

local notation "Acris" => ACris.ACris ℂ_[l] l

def cD : Acris →+* Per6.BdR l := (algebraMap (Per6.BdRp l) (Per6.BdR l)).comp (ACris.iota ℂ_[l] l)

theorem cD_injective : Function.Injective (cD l) :=
  (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)).comp
    (ACris.iota_injective (K := ℂ_[l]) (p := l))

theorem cD_l_ne_zero : cD l (l : Acris) ≠ 0 := by
  intro h
  have h1 : (l : Acris) = 0 := cD_injective l (h.trans (map_zero _).symm)
  have h2 := congrArg (ACris.iota ℂ_[l] l) h1
  rw [map_natCast, map_zero] at h2
  exact (IsPerfectoidField.isUnit_natCast_p_bDeRhamPlus (K := ℂ_[l]) l).ne_zero h2

theorem cD_tA : cD l (Per6.tA l) = algebraMap (Per6.BdRp l) (Per6.BdR l) (tBdR l) :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem cD_tA_ne_zero : cD l (Per6.tA l) ≠ 0 := by
  rw [cD_tA]
  exact algebraMap_tBdR_ne_zero

def ιCD : Per6.Bcris l →+* Per6.BdR l := liftF (cD l) (cD_l_ne_zero l) (cD_tA_ne_zero l)

theorem ιCD_fac : Fac (ιCD l) (Per6.cB l) (cD l) := liftF_fac _ _ _

variable {l} in
theorem ιCD_cB (x : Acris) : ιCD l (Per6.cB l x) = cD l x := ιCD_fac l x

variable {l} in
theorem cD_apply (x : Acris) :
    cD l x = algebraMap (Per6.BdRp l) (Per6.BdR l) (ACris.iota ℂ_[l] l x) := rfl

theorem ιCD_inj : Inj (ιCD l) :=
  liftF_inj _ _ _ (cD_injective l)

variable {l} in
theorem ιCD_injective : Function.Injective (ιCD l) := ιCD_inj l

theorem cB_isFrac : IsFrac (Per6.cB l) (l : Acris) (Per6.tA l) := loc2_isFrac

theorem isUnit_cB_l : IsUnit (Per6.cB l (l : Acris)) := (cB_isFrac l).1

variable {l} in

theorem bcris_surj (x : Per6.Bcris l) : ∃ (m n : ℕ) (y : Acris),
    Per6.cB l (l : Acris) ^ m * Per6.cB l (Per6.tA l) ^ n * x = Per6.cB l y :=
  (cB_isFrac l).2.2 x

variable {l} in
theorem bcris_hom_ext {E : Type} [Semiring E] {f g : Per6.Bcris l →+* E}
    (h : ∀ x, f (Per6.cB l x) = g (Per6.cB l x)) : f = g :=
  (cB_isFrac l).hom_ext h

theorem φB_comp : (Per6.φB l).comp (Per6.cB l) = (Per6.cB l).comp (ACris.phi ℂ_[l] l) :=
  loc2_map_comp _ _ _ _ _

variable {l} in
theorem φB_cB (x : Acris) : Per6.φB l (Per6.cB l x) = Per6.cB l (ACris.phi ℂ_[l] l x) :=
  ((RingHom.comp_apply _ _ x).symm.trans (RingHom.congr_fun (φB_comp l) x)).trans
    (RingHom.comp_apply _ _ x)

variable {l} in
theorem σB_comp (g : GQ l) :
    (Per6.σB g).comp (Per6.cB l) = (Per6.cB l).comp (ACris.galCris (Per6.toBot g)) :=
  loc2_map_comp _ _ _ _ _

variable {l} in
theorem σB_cB (g : GQ l) (x : Acris) :
    Per6.σB g (Per6.cB l x) = Per6.cB l (ACris.galCris (Per6.toBot g) x) :=
  ((RingHom.comp_apply _ _ x).symm.trans (RingHom.congr_fun (σB_comp g) x)).trans
    (RingHom.comp_apply _ _ x)

theorem kur_eq : MaximalUnramifiedExtension l = unramifiedClosure l := by
  unfold MaximalUnramifiedExtension unramifiedClosure primeToPRoots
  congr 1
  ext x
  refine exists_congr fun m => and_congr_right fun _ => and_congr_left fun _ => ?_
  rw [Nat.coprime_comm, (Fact.out : l.Prime).coprime_iff_not_dvd]

def oD : Om l →+* Per6.BdR l := algClToBdRField l

variable {l} in

theorem exists_iota_eq (y : ACris.BCrisPlus ℂ_[l] l) : ∃ (k : ℕ) (a : Acris),
    ACris.iota ℂ_[l] l a = ACris.iota ℂ_[l] l (l : Acris) ^ k * ACris.iotaPlus ℂ_[l] l y :=
  away_exists (ACris.iotaPlus ℂ_[l] l) (ACris.iota ℂ_[l] l) ACris.iotaPlus_algebraMap y

variable {l} in
theorem exists_ιCD_eq_iotaPlus (y : ACris.BCrisPlus ℂ_[l] l) :
    ∃ b, ιCD l b = algebraMap (Per6.BdRp l) (Per6.BdR l) (ACris.iotaPlus ℂ_[l] l y) := by
  obtain ⟨k, a, h⟩ := exists_iota_eq y
  have e : cD l a = cD l (l : Acris) ^ k *
      algebraMap (Per6.BdRp l) (Per6.BdR l) (ACris.iotaPlus ℂ_[l] l y) := by
    rw [cD_apply, cD_apply, h, map_mul, map_pow]
  rw [← ιCD_cB, ← ιCD_cB] at e
  exact exists_map_eq_of_pow_mul (ιCD l) (isUnit_cB_l l) e

theorem exists_ιCD_eq (c : ↥(MaximalUnramifiedExtension l)) : ∃ b, ιCD l b = ((oD l).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))) c := by
  obtain ⟨y, hy⟩ := (ACris.mem_algClInBCrisPlus (p := l)).1
    (ACris.unramifiedClosure_le ((kur_eq l).le c.2))
  obtain ⟨b, hb⟩ := exists_ιCD_eq_iotaPlus y
  exact ⟨b, hb.trans (congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) hy)⟩

def uB : ↥(MaximalUnramifiedExtension l) →+* Per6.Bcris l :=
  pullHom (ιCD l) ιCD_injective ((oD l).comp (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))) (exists_ιCD_eq l)

variable {l} in
theorem ιCD_uB (c : ↥(MaximalUnramifiedExtension l)) : ιCD l (uB l c) = oD l (c : Om l) :=
  map_pullHom _ _ _ (exists_ιCD_eq l) c

def qB : ℚ_[l] →+* Per6.Bcris l := (uB l).comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))

variable {l} in
theorem ιCD_qB (q : ℚ_[l]) : ιCD l (qB l q) = oD l (algebraMap ℚ_[l] (Om l) q) :=
  ιCD_uB _

variable {l} in
theorem uB_algebraMap (q : ℚ_[l]) : uB l (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = qB l q := rfl

def tB : Per6.Bcris l := Per6.cB l (Per6.tA l)

def toBotHom : GQ l →* (Om l ≃ₐ[(⊥ : IntermediateField ℚ_[l] (Om l))] Om l) where
  toFun := Per6.toBot
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

def χQ : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp ((cycloChar ⊥).comp (toBotHom l))

def actC : GQ l →* (ℂ_[l] ≃+* ℂ_[l]) := (galCpHom (K := ⊥)).comp (toBotHom l)

def tiltInv : PreTilt ↥(normInteger ℂ_[l]) l →+* OCb l :=
  Perfection.map l (Per6.modPEquiv l).symm.toRingHom

theorem tiltMap_tiltInv (x : PreTilt ↥(normInteger ℂ_[l]) l) : Per6.tiltMap l (tiltInv l x) = x :=
  Perfection.ext fun _ => (Per6.modPEquiv l).apply_symm_apply _

theorem tiltInv_tiltMap (x : OCb l) : tiltInv l (Per6.tiltMap l x) = x :=
  Perfection.ext fun _ => (Per6.modPEquiv l).symm_apply_apply _

def tiltEquiv : OCb l ≃+* PreTilt ↥(normInteger ℂ_[l]) l :=
  RingEquiv.ofRingHom (Per6.tiltMap l) (tiltInv l) (RingHom.ext (tiltMap_tiltInv l))
    (RingHom.ext (tiltInv_tiltMap l))

variable {l} in

def galT (g : GQ l) : OCb l →+* OCb l :=
  (tiltInv l).comp ((preTiltMap l (galCp (Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (AInf.norm_galCp_toRingHom (Per6.toBot g))).comp (Per6.tiltMap l))

def ζO (n : ℕ) : OC l := (Per6.intEquiv l).symm (rootSeqInt l n)

def εO : OCb l := tiltInv l (epsilon l)

end PositivityTheory.LocInh
