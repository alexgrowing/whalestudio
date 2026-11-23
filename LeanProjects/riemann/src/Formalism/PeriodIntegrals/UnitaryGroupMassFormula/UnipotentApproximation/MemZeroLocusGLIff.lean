import Mathlib
import Formalism.UnipotentAdelicQuotients.UnipotentStrongApprox

open NumberField IsDedekindDomain

namespace PI.UnipApproxD

def Pts {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) (R : Type) [CommRing R]
    [Algebra F R] (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P = 0

noncomputable def mexp (F : Type) [Field F] {R : Type} [CommRing R] [Algebra F R] (n : ℕ)
    (X : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ k ∈ Finset.range n, ((k.factorial : F)⁻¹) • X ^ k

def lc {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R] {n d : ℕ}
    (X : Fin d → Matrix (Fin n) (Fin n) F) (a : Fin d → R) : Matrix (Fin n) (Fin n) R :=
  ∑ i, a i • (X i).map (algebraMap F R)

def ExpParam (F : Type) [Field F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∃ (d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F),
    (∀ (R : Type) [CommRing R] [Algebra F R] (a : Fin d → R),
      (lc X a) ^ n = 0 ∧ Pts S R (mexp F n (lc X a))) ∧
    (∀ (R : Type) [CommRing R] [Algebra F R],
      (∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ((g : Matrix (Fin n) (Fin n) R) - 1) ^ n = 0) →
      ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ∃ a : Fin d → R, (g : Matrix (Fin n) (Fin n) R) = mexp F n (lc X a))

def CoreExp : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ExpParam F n S

def UnipAdele : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S (FiniteAdeleRing (𝓞 F) F),
      ((g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) - 1) ^ n = 0

def AddDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], DenseRange (algebraMap F (FiniteAdeleRing (𝓞 F) F))

end PI.UnipApproxD
