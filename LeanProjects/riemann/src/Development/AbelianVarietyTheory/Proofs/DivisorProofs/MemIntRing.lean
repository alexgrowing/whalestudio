import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV

noncomputable section

open IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.TauNorm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum ℤ)

abbrev Av : Type := v.adicCompletion ℚ ⊗[ℚ] K

abbrev bas : Module.Basis (Fin (Module.finrank ℚ K)) (v.adicCompletion ℚ) (Av K v) :=
  Algebra.TensorProduct.basis (v.adicCompletion ℚ) (Module.finBasis ℚ K)

def IsInt (x : Av K v) : Prop := ∀ i, (bas K v).repr x i ∈ v.adicCompletionIntegers ℚ

abbrev sig (τ : K ≃ₐ[ℚ] K) : Av K v →ₐ[ℚ] Av K v :=
  Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) (τ : K →ₐ[ℚ] K)

variable {K v}

theorem isInt_zero : IsInt K v 0 := fun i => by simp

theorem isInt_add {x y : Av K v} (hx : IsInt K v x) (hy : IsInt K v y) : IsInt K v (x + y) :=
  fun i => by simpa only [map_add, Finsupp.add_apply] using add_mem (hx i) (hy i)

theorem isInt_neg {x : Av K v} (hx : IsInt K v x) : IsInt K v (-x) :=
  fun i => by simpa only [map_neg, Finsupp.neg_apply] using neg_mem (hx i)

variable (K v)

def intRing (h1 : IsInt K v 1) (hm : ∀ x y, IsInt K v x → IsInt K v y → IsInt K v (x * y)) :
    Subring (Av K v) where
  carrier := {x | IsInt K v x}
  mul_mem' hx hy := hm _ _ hx hy
  one_mem' := h1
  add_mem' hx hy := isInt_add hx hy
  zero_mem' := isInt_zero
  neg_mem' hx := isInt_neg hx

end GlobalTheory.TauNorm
