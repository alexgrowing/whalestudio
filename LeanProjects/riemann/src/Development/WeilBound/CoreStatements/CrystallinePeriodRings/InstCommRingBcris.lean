import Mathlib
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.BdRTGalois
import GroundTheory.PAdicHodge.BdRField

noncomputable section

namespace Formalism.Per6

open GroundTheory.PAdicHodge

section Loc2

variable {A : Type} [CommRing A] (a t : A)

def Loc2 : Type := Localization.Away (algebraMap A (Localization.Away a) t)

instance instCommRingLoc2 : CommRing (Loc2 a t) :=
  (inferInstance : CommRing (Localization.Away (algebraMap A (Localization.Away a) t)))

def Loc2.mk₁ : Localization.Away a →+* Loc2 a t :=
  algebraMap (Localization.Away a) (Localization.Away (algebraMap A (Localization.Away a) t))

def Loc2.mk₀ : A →+* Loc2 a t := (Loc2.mk₁ a t).comp (algebraMap A (Localization.Away a))

theorem Loc2.isUnit_left : IsUnit (Loc2.mk₀ a t a) :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).map (Loc2.mk₁ a t)

theorem Loc2.isUnit_right : IsUnit (Loc2.mk₀ a t t) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away (algebraMap A (Localization.Away a) t))
    (algebraMap A (Localization.Away a) t)

variable {a t}

def Loc2.lift {E : Type} [CommRing E] (f : A →+* E) (ha : IsUnit (f a)) (ht : IsUnit (f t)) :
    Loc2 a t →+* E :=
  Localization.awayLift (Localization.awayLift f a ha) (algebraMap A (Localization.Away a) t)
    ((congrArg IsUnit (IsLocalization.lift_eq (M := Submonoid.powers a)
      (S := Localization.Away a) _ t)).mpr ht)

theorem Loc2.lift_mk₀ {E : Type} [CommRing E] (f : A →+* E) (ha : IsUnit (f a)) (ht : IsUnit (f t))
    (x : A) : Loc2.lift f ha ht (Loc2.mk₀ a t x) = f x :=
  (IsLocalization.lift_eq (M := Submonoid.powers (algebraMap A (Localization.Away a) t))
    (S := Localization.Away (algebraMap A (Localization.Away a) t)) _ _).trans
    (IsLocalization.lift_eq (M := Submonoid.powers a) (S := Localization.Away a) _ x)

theorem Loc2.hom_ext {E : Type} [CommRing E] {f g : Loc2 a t →+* E}
    (h : ∀ x, f (Loc2.mk₀ a t x) = g (Loc2.mk₀ a t x)) : f = g :=
  IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A (Localization.Away a) t))
    (S := Localization.Away (algebraMap A (Localization.Away a) t))
    (IsLocalization.ringHom_ext (Submonoid.powers a) (S := Localization.Away a) (RingHom.ext h))

def Loc2.map (f : A →+* A) (ha : f a = a) (c : A) (hc : IsUnit (Loc2.mk₀ a t c)) (ht : f t = c * t) :
    Loc2 a t →+* Loc2 a t :=
  Loc2.lift ((Loc2.mk₀ a t).comp f)
    (by rw [RingHom.comp_apply, ha]; exact Loc2.isUnit_left a t)
    (by rw [RingHom.comp_apply, ht, map_mul]; exact hc.mul (Loc2.isUnit_right a t))

theorem Loc2.map_mk₀ (f : A →+* A) (ha : f a = a) (c : A) (hc : IsUnit (Loc2.mk₀ a t c))
    (ht : f t = c * t) (x : A) : Loc2.map f ha c hc ht (Loc2.mk₀ a t x) = Loc2.mk₀ a t (f x) :=
  Loc2.lift_mk₀ _ _ _ x

end Loc2

variable (l : ℕ) [Fact l.Prime]

local notation "Acris" => ACris.ACris ℂ_[l] l

def intEquiv : ↥(PadicComplexInt l) ≃+* ↥(normInteger ℂ_[l]) where
  toFun x := ⟨x.1, mem_normInteger.2 ((mem_padicComplexInt_iff x.1).1 x.2)⟩
  invFun x := ⟨x.1, (mem_padicComplexInt_iff x.1).2 (mem_normInteger.1 x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem not_isUnit_l : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := fun h => by
  have h1 := h.map (intEquiv l)
  rw [map_natCast] at h1
  exact (Fact.out : ¬ IsUnit ((l : ℕ) : normInteger ℂ_[l])) h1

scoped instance factNotUnit : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨not_isUnit_l l⟩

def modPEquiv : ModP ↥(PadicComplexInt l) l ≃+* ModP ↥(normInteger ℂ_[l]) l :=
  Ideal.quotientEquiv _ _ (intEquiv l) (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2)

def tiltMap : PreTilt ↥(PadicComplexInt l) l →+* PreTilt ↥(normInteger ℂ_[l]) l :=
  Perfection.map l (modPEquiv l).toRingHom

def ainfMap : WittVector l (PreTilt ↥(PadicComplexInt l) l) →+* AInf ℂ_[l] l :=
  WittVector.map (tiltMap l)

abbrev BdRp : Type := BDeRhamPlus ↥(normInteger ℂ_[l]) l

abbrev BdR : Type := BDeRham ↥(normInteger ℂ_[l]) l

def tA : Acris := ACris.periodT (untilt_epsilon (p := l))

def Bcris : Type := Loc2 (l : Acris) (tA l)

instance instCommRingBcris : CommRing (Bcris l) := instCommRingLoc2 (l : Acris) (tA l)

def cB : Acris →+* Bcris l := Loc2.mk₀ (l : Acris) (tA l)

def aB : WittVector l (PreTilt ↥(PadicComplexInt l) l) →+* Bcris l :=
  ((cB l).comp (algebraMap (AInf ℂ_[l] l) Acris)).comp (ainfMap l)

def aD : WittVector l (PreTilt ↥(PadicComplexInt l) l) →+* BdRp l :=
  (wittToBDeRhamPlus ↥(normInteger ℂ_[l]) l).comp (ainfMap l)

def zA : ℤ_[l] →+* WittVector l (PreTilt ↥(PadicComplexInt l) l) :=
  (WittVector.map (ZMod.castHom (dvd_refl l) (PreTilt ↥(PadicComplexInt l) l))).comp
    (WittVector.equiv l).symm.toRingHom

def zB : ℤ_[l] →+* Bcris l := (aB l).comp (zA l)

def zD : ℤ_[l] →+* BdR l := ((algebraMap (BdRp l) (BdR l)).comp (aD l)).comp (zA l)

def θD : BdRp l →+* ℂ_[l] := IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l

def φB : Bcris l →+* Bcris l :=
  Loc2.map (ACris.phi ℂ_[l] l) (map_natCast _ l) (l : Acris) (Loc2.isUnit_left _ _)
    (ACris.phi_periodT_eq_mul (untilt_epsilon (p := l)))

def FilD (a : ℤ) : Submodule (BdRp l) (BdR l) := IsPerfectoidField.fil ℂ_[l] l a

def IsCrisDR (f : Bcris l →+* BdR l) : Prop :=
  ∀ x : Acris, f (cB l x) = algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l x)

def IsLog (ε : PreTilt ↥(PadicComplexInt l) l) (y : BdRp l) : Prop :=
  ∀ n : ℕ, y - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ (BdRp l) ((-1) ^ (i + 1) / i) *
    (aD l (WittVector.teichmuller l ε) - 1) ^ i ∈ RingHom.ker (θD l) ^ n

variable {l}

def toBot (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) :
    PadicAlgCl l ≃ₐ[(⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))] PadicAlgCl l :=
  { g.toRingEquiv with
    commutes' := fun x => by
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 x.2
      change g (x : PadicAlgCl l) = (x : PadicAlgCl l)
      rw [← hq, AlgEquiv.commutes] }

def χA {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) : Acris :=
  algebraMap (AInf ℂ_[l] l) Acris (IsPerfectoidField.padicIntToWitt l (cycloChar K σ : ℤ_[l]))

theorem isUnit_χA {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) : IsUnit (χA σ) :=
  ((cycloChar K σ).isUnit.map (IsPerfectoidField.padicIntToWitt l)).map _

theorem galCris_tA {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) : ACris.galCris σ (tA l) = χA σ * tA l := by
  apply ACris.iota_injective (K := ℂ_[l]) (p := l)
  rw [← ACris.gal_smul_def, tA, ACris.iota_gal_smul, ACris.iota_periodT, map_mul, ACris.iota_periodT,
    χA, ACris.iota_padicInt, gal_smul_fontaineT]

def σB (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : Bcris l →+* Bcris l :=
  Loc2.map (ACris.galCris (toBot g)) (map_natCast _ l) (χA (toBot g))
    ((isUnit_χA (toBot g)).map _) (galCris_tA (toBot g))

def σD (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : BdR l ≃+* BdR l :=
  galBdRField (toBot g)

end Formalism.Per6
