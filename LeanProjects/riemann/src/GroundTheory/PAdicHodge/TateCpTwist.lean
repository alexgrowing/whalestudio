import Mathlib
import GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace

variable {p : ℕ} [Fact p.Prime]

instance uniformContinuousConstSMul_intermediateField
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : UniformContinuousConstSMul K (PadicAlgCl p) :=
  ⟨fun k => by
    have h : (fun y : PadicAlgCl p => k • y) = fun y => (k : PadicAlgCl p) * y := funext fun _ => rfl
    rw [h]
    exact uniformContinuous_addMonoidHom_of_continuous (f := AddMonoidHom.mulLeft (k : PadicAlgCl p))
      (continuous_const.mul continuous_id)⟩

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_cp (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := rfl

instance : IsScalarTower K (PadicAlgCl p) ℂ_[p] := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem continuous_algebraMap_intermediateField_cp : Continuous (algebraMap K ℂ_[p]) :=
  (Completion.continuous_coe _).comp continuous_subtype_val

instance : ContinuousSMul K ℂ_[p] :=
  ⟨by
    have h : (fun q : K × ℂ_[p] => q.1 • q.2) = fun q => algebraMap K ℂ_[p] q.1 * q.2 :=
      funext fun q => Algebra.smul_def _ _
    rw [h]
    exact ((continuous_algebraMap_intermediateField_cp K).comp continuous_fst).mul continuous_snd⟩

theorem gal_smul_algebraMap_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K ℂ_[p] k = algebraMap K ℂ_[p] k :=
  gal_smul_coe_of_mem σ k

theorem gal_smul_smul_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) (x : ℂ_[p]) :
    σ • (k • x) = k • (σ • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField]

noncomputable def cycloChar : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p))

theorem continuous_cycloChar : Continuous (cycloChar K) :=
  cyclotomicCharacter.continuous p K (PadicAlgCl p)

theorem cycloChar_spec (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val :=
  cyclotomicCharacter.spec p (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p) σ) ζ hζ

noncomputable def twistScalar (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

theorem twistScalar_one (j : ℤ) : twistScalar K j 1 = 1 := by
  simp [twistScalar]

theorem twistScalar_mul (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    twistScalar K j (σ * τ) = twistScalar K j σ * twistScalar K j τ := by
  simp only [twistScalar, map_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem twistScalar_zero (σ : Gal(PadicAlgCl p/K)) : twistScalar K 0 σ = 1 := by
  simp [twistScalar]

theorem gal_smul_twistScalar (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    σ • twistScalar K j τ = twistScalar K j τ :=
  gal_smul_algebraMap σ _

noncomputable def cpTwistMap (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] →L[K] ℂ_[p] where
  toFun x := twistScalar K j σ * (σ • x)
  map_add' x y := by rw [smul_add, mul_add]
  map_smul' k x := by
    rw [gal_smul_smul_intermediateField, RingHom.id_apply, mul_smul_comm]
  cont := continuous_const.mul (continuous_const_smul σ)

theorem cpTwistMap_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistMap K j σ x = twistScalar K j σ * (σ • x) := rfl

noncomputable def cpTwistRep (j : ℤ) : ContRepresentation K Gal(PadicAlgCl p/K) ℂ_[p] :=
  .ofMonoidHom
    { toFun := cpTwistMap K j
      map_one' := by
        ext x
        simp [cpTwistMap_apply, twistScalar_one]
      map_mul' := fun σ τ => by
        ext x
        change cpTwistMap K j (σ * τ) x = cpTwistMap K j σ (cpTwistMap K j τ x)
        simp only [cpTwistMap_apply, twistScalar_mul, smul_mul', gal_smul_twistScalar, mul_smul]
        ring }

noncomputable abbrev cpTwist (j : ℤ) : TopRep K Gal(PadicAlgCl p/K) := TopRep.of (cpTwistRep K j)

theorem cpTwistRep_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistRep K j σ x = twistScalar K j σ * (σ • x) := rfl

theorem cpTwist_ρ_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    (cpTwist K j).ρ σ x = twistScalar K j σ * (σ • x) := rfl

end GroundTheory.PAdicHodge
