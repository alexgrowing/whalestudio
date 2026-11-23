import Mathlib

noncomputable section
namespace GlobalTheory.DenseSec

def EtChart (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {g : ℕ} (t : Fin g → A) (h : A) : Prop :=
  letI : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h)

def pt {R A Ω : Type} [CommRing R] [CommRing A] [Algebra R A] [Field Ω] [Algebra R Ω] (a : A →ₐ[R] Ω) :
    TensorProduct R Ω A →ₐ[Ω] Ω :=
  Algebra.TensorProduct.lift (AlgHom.id Ω Ω) a (fun _ _ => Commute.all _ _)

end GlobalTheory.DenseSec
