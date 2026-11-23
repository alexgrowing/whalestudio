import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      W.comap (liftForm (ι := ι) (J := J) (R := O)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes

def BlowUpHorizontalChartLength.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W ≠ 0 →
      (C ϖ : MRing (extIdx ι J) O) ∉ W →
      ∀ hW : W.IsPrime,
      haveI := hW
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) W =
        Module.length
          (Localization.AtPrime ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
            (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))
          (LocalizedModule ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
              (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))).primeCompl
            (Polynomial (MRing ι O) ⧸
              (P ⊔ Ideal.span {x}).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O))))

def PolynomialLocalizedLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime] (I : Ideal R),
    Module.length (Localization.AtPrime (q.map (Polynomial.C : R →+* Polynomial R)))
        (LocalizedModule (q.map (Polynomial.C : R →+* Polynomial R)).primeCompl
          (Polynomial R ⧸ I.map (Polynomial.C : R →+* Polynomial R))) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
