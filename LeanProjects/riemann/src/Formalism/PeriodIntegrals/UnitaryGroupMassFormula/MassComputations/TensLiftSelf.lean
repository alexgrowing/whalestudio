import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def pv (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : Fin n → Fv F v ⊗[F] E :=
  fun i => tensMap (E := E) (evalV F v) (x i)

def latHat (Λ : Set (Fin n → E)) : Set (Fin n → Af F ⊗[F] E) :=
  {x | ∀ v, pv v x ∈ latLoc (E := E) v Λ}

theorem pv_mulVec (v : HeightOneSpectrum (𝓞 F)) (m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (x : Fin n → Af F ⊗[F] E) :
    pv v (m *ᵥ x) = (m.map (tensMap (E := E) (evalV F v))) *ᵥ pv v x := by
  funext i
  simp [pv, Matrix.mulVec, dotProduct, map_sum]

open Classical in
theorem singleV_smul (v : HeightOneSpectrum (𝓞 F)) (c : F) (y : Fv F v) :
    singleV F v (c • y) = c • singleV F v y := by
  apply RestrictedProduct.ext
  intro j
  show (singleV F v (c • y)) j = evalV F j (c • singleV F v y)
  rw [map_smul]
  show _ = c • (singleV F v y) j
  by_cases h : j = v
  · subst h
    rw [PI.VolStabSW.VolAAW.singleV_self, PI.VolStabSW.VolAAW.singleV_self]
  · rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, PI.VolStabSW.VolAAW.singleV_ne _ _ h, smul_zero]

def sV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' := PI.VolStabSW.SdUniqW.singleV_add v
  map_smul' := singleV_smul v

def liftV (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : Fin n → Af F ⊗[F] E :=
  fun i => LinearMap.rTensor E (sV v) (y i)

theorem tens_lift_self (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F v) (LinearMap.rTensor E (sV v) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F v (singleV F v a)) ⊗ₜ[F] e = a ⊗ₜ e
    show (singleV F v a v) ⊗ₜ[F] e = a ⊗ₜ e
    rw [PI.VolStabSW.VolAAW.singleV_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tens_lift_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F w) (LinearMap.rTensor E (sV v) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F w (singleV F v a)) ⊗ₜ[F] e = 0
    show (singleV F v a w) ⊗ₜ[F] e = 0
    rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem pv_liftV_self (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : pv v (liftV v y) = y := by
  funext i
  exact tens_lift_self v (y i)

theorem pv_liftV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fin n → Fv F v ⊗[F] E) :
    pv w (liftV v y) = 0 := by
  funext i
  exact tens_lift_ne h (y i)

theorem liftV_mem (Λ : Set (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : liftV v y ∈ latHat (F := F) Λ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [pv_liftV_self]
    exact hy
  · rw [pv_liftV_ne h]
    exact zero_mem _

theorem loc_of_matStab (Λ : Set (Fin n → E)) {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)}
    (hm : m ∈ matStab (latHat (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : (m.map (tensMap (E := E) (evalV F v))) *ᵥ y ∈ latLoc (E := E) v Λ := by
  have h := hm _ (liftV_mem Λ v hy) v
  rwa [pv_mulVec, pv_liftV_self] at h

end Lift

end MassDataMassesW.KCptW
