import Mathlib
import GroundTheory.PAdicHodge.ACrisBdRGalois
import GroundTheory.PAdicHodge.BdRTGalois
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section AwayAction

variable {G R : Type*} [Monoid G] [CommRing R] [MulSemiringAction G R] (t : R)

def awaySMulHom (h : ∀ σ : G, IsUnit (algebraMap R (Localization.Away t) (σ • t))) (σ : G) :
    Localization.Away t →+* Localization.Away t :=
  Localization.awayLift
    ((algebraMap R (Localization.Away t)).comp (MulSemiringAction.toRingHom G R σ)) t (h σ)

variable {t} (h : ∀ σ : G, IsUnit (algebraMap R (Localization.Away t) (σ • t)))

theorem awaySMulHom_algebraMap (σ : G) (x : R) :
    awaySMulHom t h σ (algebraMap R (Localization.Away t) x) =
      algebraMap R (Localization.Away t) (σ • x) :=
  IsLocalization.lift_eq _ x

theorem awaySMulHom_one : awaySMulHom t h (1 : G) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, awaySMulHom_algebraMap, one_smul, RingHom.comp_apply, RingHom.id_apply]

theorem awaySMulHom_mul (σ τ : G) :
    awaySMulHom t h (σ * τ) = (awaySMulHom t h σ).comp (awaySMulHom t h τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers t)
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, awaySMulHom_algebraMap, mul_smul, RingHom.comp_apply, RingHom.comp_apply,
    awaySMulHom_algebraMap, awaySMulHom_algebraMap]

def awayMulSemiringAction : MulSemiringAction G (Localization.Away t) where
  smul σ x := awaySMulHom t h σ x
  one_smul x := by
    change awaySMulHom t h 1 x = x
    rw [awaySMulHom_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change awaySMulHom t h (σ * τ) x = awaySMulHom t h σ (awaySMulHom t h τ x)
    rw [awaySMulHom_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (awaySMulHom t h σ)
  smul_add σ := map_add (awaySMulHom t h σ)
  smul_one σ := map_one (awaySMulHom t h σ)
  smul_mul σ := map_mul (awaySMulHom t h σ)

theorem awaySMulHom_comm (f : Localization.Away t →+* Localization.Away t) (F : R →+* R)
    (hf : ∀ x, f (algebraMap R (Localization.Away t) x) = algebraMap R (Localization.Away t) (F x))
    (hF : ∀ (σ : G) x, F (σ • x) = σ • F x) (σ : G) (x : Localization.Away t) :
    f (awaySMulHom t h σ x) = awaySMulHom t h σ (f x) := by
  have e : f.comp (awaySMulHom t h σ) = (awaySMulHom t h σ).comp f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    refine RingHom.ext fun y => ?_
    simp only [RingHom.comp_apply]
    rw [awaySMulHom_algebraMap, hf, hf, awaySMulHom_algebraMap, hF]
  exact congrArg (fun g => g x) e

end AwayAction

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

def chiCris (σ : Gal(PadicAlgCl p/K)) : ACris ℂ_[p] p :=
  algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p)
    (IsPerfectoidField.padicIntToWitt p (cycloChar K σ : ℤ_[p]))

theorem isUnit_chiCris (σ : Gal(PadicAlgCl p/K)) : IsUnit (chiCris σ) :=
  ((cycloChar K σ).isUnit.map (IsPerfectoidField.padicIntToWitt p)).map _

theorem gal_smul_periodT (σ : Gal(PadicAlgCl p/K)) {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    σ • periodT hε = chiCris σ * periodT hε := by
  apply iota_injective (K := ℂ_[p]) (p := p)
  rw [iota_gal_smul, iota_periodT, map_mul, iota_periodT, chiCris, iota_padicInt,
    gal_smul_fontaineT]

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)

omit hp in
theorem isUnit_map_of_eq_mul {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {x c t : A}
    (h : x = c * t) (hc : IsUnit c) (ht : IsUnit (f t)) : IsUnit (f x) := by
  rw [h, map_mul]
  exact (hc.map f).mul ht

theorem isUnit_gal_smul_periodT (σ : Gal(PadicAlgCl p/K)) :
    IsUnit (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)
      (σ • algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (periodT hε))) :=
  isUnit_map_of_eq_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    ((gal_smul_algebraMap_plus σ _).trans
      ((congrArg (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)) (gal_smul_periodT σ hε)).trans
        (map_mul _ _ _)))
    ((isUnit_chiCris σ).map _) (IsLocalization.Away.algebraMap_isUnit (S := BCris hε) _)

def galB (σ : Gal(PadicAlgCl p/K)) : BCris hε →+* BCris hε :=
  awaySMulHom _ (isUnit_gal_smul_periodT hε) σ

def galBAction : MulSemiringAction Gal(PadicAlgCl p/K) (BCris hε) :=
  awayMulSemiringAction (isUnit_gal_smul_periodT hε)

theorem galBAction_smul (σ : Gal(PadicAlgCl p/K)) (x : BCris hε) :
    (galBAction hε).smul σ x = galB hε σ x :=
  rfl

theorem galB_one : galB hε (1 : Gal(PadicAlgCl p/K)) = RingHom.id (BCris hε) :=
  awaySMulHom_one _

theorem galB_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galB hε (σ * τ) = (galB hε σ).comp (galB hε τ) :=
  awaySMulHom_mul _ σ τ

theorem galB_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : BCrisPlus ℂ_[p] p) :
    galB hε σ (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) x) =
      algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (σ • x) :=
  awaySMulHom_algebraMap (isUnit_gal_smul_periodT hε) σ x

theorem phiB_galB (σ : Gal(PadicAlgCl p/K)) (x : BCris hε) :
    phiB hε (galB hε σ x) = galB hε σ (phiB hε x) :=
  awaySMulHom_comm (isUnit_gal_smul_periodT hε) (phiB hε) (phiPlus ℂ_[p] p)
    (phiB_algebraMap hε) phiPlus_gal_smul σ x

end ACris

end GroundTheory.PAdicHodge
