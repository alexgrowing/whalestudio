import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat

noncomputable section

open NumberField GlobalTheory.BCT Matrix
open scoped Classical

namespace GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem mulMat_eq_map (a : B.A) :
    mulMat e b a = (e : K.E →+* w.adicCompletion E).mapMatrix (LinearMap.toMatrix b b (LinearMap.mulLeft K.E a)) := rfl

theorem mulMat_one : mulMat e b (1 : B.A) = 1 := by
  rw [mulMat_eq_map, LinearMap.mulLeft_one, LinearMap.toMatrix_id, map_one]

theorem mulMat_mul (a a' : B.A) : mulMat e b (a * a') = mulMat e b a * mulMat e b a' := by
  rw [mulMat_eq_map, mulMat_eq_map, mulMat_eq_map, LinearMap.mulLeft_mul, ← map_mul, ← LinearMap.toMatrix_mul]
  rfl

theorem mulMat_injective : Function.Injective (mulMat e b) := by
  intro a a' h
  have h1 : LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) = LinearMap.toMatrix b b (LinearMap.mulLeft K.E a') :=
    Matrix.map_injective e.injective h
  have h2 := congrArg (fun f : B.A →ₗ[K.E] B.A => f 1) ((LinearMap.toMatrix b b).injective h1)
  simpa using h2

def mulU : B.Aˣ →* GLw m w where
  toFun a := ⟨mulMat e b a, mulMat e b ((a⁻¹ : B.Aˣ) : B.A),
    by rw [← mulMat_mul, Units.mul_inv, mulMat_one], by rw [← mulMat_mul, Units.inv_mul, mulMat_one]⟩
  map_one' := Units.ext (mulMat_one e b)
  map_mul' a a' := Units.ext (mulMat_mul e b _ _)

theorem mulU_val (a : B.Aˣ) : (mulU e b a).val = mulMat e b a := rfl

theorem mulU_injective : Function.Injective (mulU e b) :=
  fun _ _ h => Units.ext (mulMat_injective e b (congrArg Units.val h))

end GlobalTheory.TwLat
