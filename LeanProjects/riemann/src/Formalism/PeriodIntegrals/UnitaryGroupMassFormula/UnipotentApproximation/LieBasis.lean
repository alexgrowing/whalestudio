import Mathlib
import Formalism.UnipotentAdelicQuotients.UnipotentStrongApprox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.MemZeroLocusGLIff

open NumberField IsDedekindDomain

namespace PI.UnipApproxD

def Lie {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) (R : Type) [CommRing R]
    [Algebra F R] : Set (Matrix (Fin n) (Fin n) R) :=
  {X | Pts S (DualNumber R) (1 + X.map (TrivSqZeroExt.inr : R → DualNumber R))}

noncomputable def mlog (F : Type) [Field F] {R : Type} [CommRing R] [Algebra F R] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  ∑ k ∈ Finset.Ico 1 n, ((-1 : F) ^ (k + 1) / (k : F)) • (M - 1) ^ k

def LieLin : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), HeckeCharacterZeroLocus.IsGroupLocus S →
    ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F),
      (∀ i, X i ∈ Lie S F) → ∀ a : Fin d → R, lc X a ∈ Lie S R

def LieBasis : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), HeckeCharacterZeroLocus.IsGroupLocus S →
    ∃ (d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F), (∀ i, X i ∈ Lie S F) ∧
      ∀ (R : Type) [CommRing R] [Algebra F R], ∀ Y ∈ Lie S R, ∃ a : Fin d → R, Y = lc X a

def LieToG : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    ∀ (R : Type) [CommRing R] [Algebra F R], ∀ X ∈ Lie S R, X ^ n = 0 → Pts S R (mexp F n X)

def LieNilp : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ X ∈ Lie S F, X ^ n = 0

def GToLie : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    ∀ (R : Type) [CommRing R] [Algebra F R], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R,
      ((g : Matrix (Fin n) (Fin n) R) - 1) ^ n = 0 → mlog F n (g : Matrix (Fin n) (Fin n) R) ∈ Lie S R

def ExpLog : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (R : Type) [CommRing R] [Algebra F R]
    (M : Matrix (Fin n) (Fin n) R), (M - 1) ^ n = 0 →
      mexp F n (mlog F n M) = M ∧ (mlog F n M) ^ n = 0

def PolyNilp : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F),
    (∀ b : Fin d → F, (lc X b) ^ n = 0) →
    ∀ (R : Type) [CommRing R] [Algebra F R] (a : Fin d → R), (lc X a) ^ n = 0

end PI.UnipApproxD
