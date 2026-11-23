import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFactsStatement

namespace GlobalTheory.UnitLemma.Witt

open GlobalTheory.UnitLemma Polynomial

theorem exists_conj (K : UQ) : ∃ s : K.O →+* K.O,
    ∀ x, algebraMap K.O K.E (s x) = K.c (algebraMap K.O K.E x) := by
  choose f hf using K.c_int
  have inj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  refine ⟨{ toFun := f
            map_one' := inj (by rw [← hf]; simp)
            map_mul' := fun x y => inj (by rw [map_mul, ← hf, ← hf, ← hf]; simp)
            map_zero' := inj (by rw [← hf]; simp)
            map_add' := fun x y => inj (by rw [map_add, ← hf, ← hf, ← hf]; simp) }, fun x => (hf x).symm⟩

end GlobalTheory.UnitLemma.Witt
