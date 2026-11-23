import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain

open IsLocalRing

namespace UpperTheory.V.AlgebraTools.Conn

def Reg2 {A : Type} [CommRing A] (J : Ideal A) (u v : A) : Prop :=
  (∀ a, u * a ∈ J → a ∈ J) ∧ ∀ a, v * a ∈ J ⊔ Ideal.span {u} → a ∈ J ⊔ Ideal.span {u}

def ConnOn {R : Type} [CommRing R] (a : Ideal R) (k : WithBot ℕ∞) : Prop :=
  ∀ I : Ideal R, a ≤ I → ringKrullDim (R ⧸ I) < k →
    IsConnected (PrimeSpectrum.zeroLocus (a : Set R) \ PrimeSpectrum.zeroLocus (I : Set R))

structure IsBase (A : Type) [CommRing A] [IsLocalRing A] : Prop where
  dom : IsDomain A
  normal : IsIntegrallyClosed A
  cm : ReciprocityTheory.CA.IsCM A
  complete : IsAdicComplete (maximalIdeal A) A

def HasBase (R : Type) [CommRing R] : Prop :=
  ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (i : A →+* R),
    IsBase A ∧ Function.Injective i ∧ i.Finite

def CohenType (R : Type) [CommRing R] : Prop :=
  ∀ p : Ideal R, p.IsPrime → HasBase (R ⧸ p)

theorem isBase_field (K : Type) [Field K] : IsBase K where
  dom := inferInstance
  normal := inferInstance
  cm := ⟨inferInstance, 0, by simp [ringKrullDim_eq_zero_of_field], [], rfl, by simp,
    RingTheory.Sequence.IsRegular.nil K K⟩
  complete := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance

theorem HasBase.of_ringEquiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : HasBase R) : HasBase S := by
  obtain ⟨A, _, _, i, hA, hi, hf⟩ := h
  exact ⟨A, inferInstance, inferInstance, e.toRingHom.comp i, hA, e.injective.comp hi,
    (RingHom.Finite.of_surjective _ e.surjective).comp hf⟩

theorem isWeaklyRegularPairMod_one_left {A : Type} [CommRing A] (J : Ideal A) (v : A) : Reg2 J 1 v :=
  ⟨fun a h => by simpa using h, fun a _ => by simp⟩

end UpperTheory.V.AlgebraTools.Conn
