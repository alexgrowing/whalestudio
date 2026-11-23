import Mathlib

noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

def FiniteFreeHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  letI := φ.toAlgebra
  Module.Free A B ∧ Module.Finite A B

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
