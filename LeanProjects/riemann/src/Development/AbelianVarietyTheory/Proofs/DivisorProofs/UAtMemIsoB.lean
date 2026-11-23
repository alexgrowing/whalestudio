import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.VanishLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def liftT (v : Pl F) : Fv F v ⊗[F] E →ₗ[F] AE F E := (GlobalTheory.LatVac.liftV v).rTensor E

variable {n n₁ d d₁ : ℕ}

def uAt (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E) : Matrix (Fin n) (Fin d) (AE F E) :=
  Matrix.vecMulVec (incV F H.x) (liftT v t • incV F H'.y)

theorem at_liftT (v : Pl F) (t : Fv F v ⊗[F] E) : At (evFin F v) (liftT v t) := by
  intro u hu
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul a e =>
    rw [liftT, LinearMap.rTensor_tmul, TensorProduct.smul_tmul', GlobalTheory.LatVac.at_liftV v a u hu, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

theorem at_uAt (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E) : At (evFin F v) (uAt H H' v t) := by
  intro u hu
  ext i j
  have h := at_liftT v t u hu
  simp only [uAt, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.zero_apply]
  rw [← mul_smul_comm, ← smul_mul_assoc, h, zero_mul, mul_zero]

theorem uAt_mem_isoB (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E) :
    uAt H H' v t ∈ isoB H H' := Or.inl ⟨_, rfl⟩

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc x w.1 w'.1, add_assoc x w'.1 w.1, add_comm w.1 w'.1]
  have e : (x + w.1) ⬝ᵥ w'.2 = x ⬝ᵥ w'.2 + w.1 ⬝ᵥ w'.2 := add_dotProduct _ _ _
  have e' : (x + w'.1) ⬝ᵥ w.2 = x ⬝ᵥ w.2 + w'.1 ⬝ᵥ w.2 := add_dotProduct _ _ _
  rw [e, e']
  have h : ψ (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) * ψ (x ⬝ᵥ w'.2 + w.1 ⬝ᵥ w'.2 + ⅟(2 : R) * (w'.1 ⬝ᵥ w'.2)) =
      ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * (ψ (x ⬝ᵥ w'.2 + ⅟(2 : R) * (w'.1 ⬝ᵥ w'.2)) *
        ψ (x ⬝ᵥ w.2 + w'.1 ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2))) := by
    simp only [← AddChar.map_add_eq_mul]
    congr 1
    ring
  linear_combination (φ (x + (w'.1 + w.1))) * h

end GlobalTheory.VanishLoc
