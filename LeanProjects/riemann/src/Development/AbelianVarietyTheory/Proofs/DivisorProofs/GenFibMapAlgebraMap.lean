import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

def genFibMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E] [Algebra T O]
    (ψ : E →ₐ[T] O) : GenFib T E →+* GenFib T O :=
  IsLocalization.map (M := Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (T := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) (GenFib T O) ψ.toRingHom (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨t, ht, (ψ.commutes t).symm⟩)

theorem genFibMap_algebraMap {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) :
    genFibMap ψ (algebraMap E (GenFib T E) e) = algebraMap O (GenFib T O) (ψ e) := by
  simp [genFibMap, IsLocalization.map_eq]

theorem genFib_ringHom_ext {T E C : Type} [CommRing T] [CommRing E] [CommRing C] [Algebra T E]
    {f g : GenFib T E →+* C} (h : ∀ e : E, f (algebraMap E _ e) = g (algebraMap E _ e)) : f = g :=
  IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid E (nonZeroDivisors T))
    (RingHom.ext h)

end GlobalTheory.LocAcyc
