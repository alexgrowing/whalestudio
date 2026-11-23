import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
