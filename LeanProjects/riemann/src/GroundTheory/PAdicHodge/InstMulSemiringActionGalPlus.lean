import Mathlib
import GroundTheory.PAdicHodge.ACrisPhi
import GroundTheory.PAdicHodge.ACrisGalois
set_option maxSynthPendingDepth 1

noncomputable section

set_option maxHeartbeats 4000000

namespace GroundTheory.PAdicHodge

namespace ACris

section Defs

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [hp : Fact p.Prime] [IsPerfectoidField K p]

abbrev BCrisPlus : Type _ := Localization.Away (p : ACris K p)

theorem phi_natCast_p : phi K p (p : ACris K p) = (p : ACris K p) :=
  map_natCast (phi K p) p

def phiPlus : BCrisPlus K p →+* BCrisPlus K p :=
  Localization.awayLift ((algebraMap (ACris K p) (BCrisPlus K p)).comp (phi K p)) (p : ACris K p)
    (by
      rw [RingHom.comp_apply, phi_natCast_p]
      exact IsLocalization.Away.algebraMap_isUnit (p : ACris K p))

variable {K p}

theorem phiPlus_algebraMap (x : ACris K p) :
    phiPlus K p (algebraMap (ACris K p) (BCrisPlus K p) x) =
      algebraMap (ACris K p) (BCrisPlus K p) (phi K p x) :=
  IsLocalization.lift_eq _ x

variable {ε : PreTilt (normInteger K) p}

abbrev BCris (hε : PreTilt.untilt ε = 1) : Type _ :=
  Localization.Away (algebraMap (ACris K p) (BCrisPlus K p) (periodT hε))

theorem isUnit_algebraMap_p_plus :
    IsUnit (algebraMap (ACris K p) (BCrisPlus K p)
      (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p))) := by
  rw [map_natCast, map_natCast]
  simpa using IsLocalization.Away.algebraMap_isUnit (S := BCrisPlus K p) (p : ACris K p)

theorem isUnit_phiPlus_periodT (hε : PreTilt.untilt ε = 1) :
    IsUnit ((algebraMap (BCrisPlus K p) (BCris hε)).comp (phiPlus K p)
      (algebraMap (ACris K p) (BCrisPlus K p) (periodT hε))) := by
  rw [RingHom.comp_apply, phiPlus_algebraMap, phi_periodT, map_mul, map_mul]
  exact (isUnit_algebraMap_p_plus.map _).mul
    (IsLocalization.Away.algebraMap_isUnit (S := BCris hε) _)

def phiB (hε : PreTilt.untilt ε = 1) : BCris hε →+* BCris hε :=
  Localization.awayLift ((algebraMap (BCrisPlus K p) (BCris hε)).comp (phiPlus K p))
    (algebraMap (ACris K p) (BCrisPlus K p) (periodT hε)) (isUnit_phiPlus_periodT hε)

theorem phiB_algebraMap (hε : PreTilt.untilt ε = 1) (x : BCrisPlus K p) :
    phiB hε (algebraMap (BCrisPlus K p) (BCris hε) x) =
      algebraMap (BCrisPlus K p) (BCris hε) (phiPlus K p x) :=
  IsLocalization.lift_eq _ x

end Defs

section Galois

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galCris_natCast_p (σ : Gal(PadicAlgCl p/K)) : galCris σ (p : ACris ℂ_[p] p) = p :=
  map_natCast (galCris σ) p

def galPlus (σ : Gal(PadicAlgCl p/K)) : BCrisPlus ℂ_[p] p →+* BCrisPlus ℂ_[p] p :=
  Localization.awayLift ((algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p)).comp (galCris σ))
    (p : ACris ℂ_[p] p)
    (by
      rw [RingHom.comp_apply, galCris_natCast_p]
      exact IsLocalization.Away.algebraMap_isUnit (p : ACris ℂ_[p] p))

theorem galPlus_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    galPlus σ (algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) x) =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (galCris σ x) :=
  IsLocalization.lift_eq _ x

theorem galPlus_one : galPlus (1 : Gal(PadicAlgCl p/K)) = RingHom.id (BCrisPlus ℂ_[p] p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p))
  ext x
  rw [RingHom.comp_apply, galPlus_algebraMap, galCris_one, RingHom.id_apply, RingHom.comp_apply,
    RingHom.id_apply]

theorem galPlus_mul (σ τ : Gal(PadicAlgCl p/K)) :
    galPlus (σ * τ) = (galPlus σ).comp (galPlus τ) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p))
  ext x
  rw [RingHom.comp_apply, galPlus_algebraMap, galCris_mul, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.comp_apply, galPlus_algebraMap, galPlus_algebraMap]

instance instMulSemiringActionGalPlus :
    MulSemiringAction Gal(PadicAlgCl p/K) (BCrisPlus ℂ_[p] p) where
  smul σ x := galPlus σ x
  one_smul x := by
    change galPlus 1 x = x
    rw [galPlus_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galPlus (σ * τ) x = galPlus σ (galPlus τ x)
    rw [galPlus_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galPlus σ)
  smul_add σ := map_add (galPlus σ)
  smul_one σ := map_one (galPlus σ)
  smul_mul σ := map_mul (galPlus σ)

theorem gal_smul_plus_def (σ : Gal(PadicAlgCl p/K)) (x : BCrisPlus ℂ_[p] p) :
    σ • x = galPlus σ x :=
  rfl

theorem gal_smul_algebraMap_plus (σ : Gal(PadicAlgCl p/K)) (x : ACris ℂ_[p] p) :
    σ • algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) x =
      algebraMap (ACris ℂ_[p] p) (BCrisPlus ℂ_[p] p) (σ • x) := by
  rw [gal_smul_plus_def, galPlus_algebraMap, gal_smul_def]

theorem phiPlus_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : BCrisPlus ℂ_[p] p) :
    phiPlus ℂ_[p] p (σ • x) = σ • phiPlus ℂ_[p] p x := by
  have h : (phiPlus ℂ_[p] p).comp (galPlus σ) = (galPlus σ).comp (phiPlus ℂ_[p] p) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ACris ℂ_[p] p))
    ext y
    simp only [RingHom.comp_apply]
    rw [galPlus_algebraMap, phiPlus_algebraMap, phiPlus_algebraMap, galPlus_algebraMap,
      ← gal_smul_def, ← gal_smul_def, phi_gal_smul]
  exact congrArg (fun f => f x) h

end Galois

end ACris

end GroundTheory.PAdicHodge
