import Mathlib
import Formalism.UnipotentAdelicQuotients.UnipotentAdelicCocompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.LieBasis

open NumberField IsDedekindDomain

namespace PI.UnipCocptD

open PI.UnipApproxD

def Above {d : ℕ} {R : Type} [Zero R] (k : ℕ) (a : Fin d → R) : Prop :=
  ∀ i : Fin d, i.val < k → a i = 0

def Malcev (F : Type) [Field F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∃ (d : ℕ) (X : Fin d → Matrix (Fin n) (Fin n) F),
    (∀ (R : Type) [CommRing R] [Algebra F R] (a : Fin d → R),
      (lc X a) ^ n = 0 ∧ Pts S R (mexp F n (lc X a))) ∧
    (∀ (R : Type) [CommRing R] [Algebra F R],
      (∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ((g : Matrix (Fin n) (Fin n) R) - 1) ^ n = 0) →
      ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S R, ∃ a : Fin d → R, (g : Matrix (Fin n) (Fin n) R) = mexp F n (lc X a)) ∧
    (∀ (R : Type) [CommRing R] [Algebra F R] (k : ℕ) (a b : Fin d → R), Above k a → Above k b →
      ∃ c : Fin d → R, Above k c ∧ mexp F n (lc X a) * mexp F n (lc X b) = mexp F n (lc X c)) ∧
    (∀ (R : Type) [CommRing R] [Algebra F R] (k : ℕ) (a b : Fin d → R), Above k a → Above k b →
      ∃ c : Fin d → R, Above (k + 1) c ∧
        mexp F n (lc X (a + b)) = mexp F n (lc X a) * mexp F n (lc X c) * mexp F n (lc X b))

def MalcevEx : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    HeckeCharacterZeroLocus.IsGroupLocus S →
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    Malcev F n S

def AdeleUnip : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)),
    (∀ (K : Type) [Field K] [Algebra F K], ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S K,
      ((g : Matrix (Fin n) (Fin n) K) - 1) ^ n = 0) →
    ∀ g ∈ HeckeCharacterZeroLocus.zeroLocusGL S (AdeleRing (𝓞 F) F),
      ((g : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 F) F)) - 1) ^ n = 0

end PI.UnipCocptD
