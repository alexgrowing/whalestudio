import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Chart

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

def chartMonomial [Fintype K] (u : ∀ k, ι k) (b : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, u k⟩ ^ b k

def chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
  aeval fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))

def chartIdeal (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) : Ideal (MRing ι F) :=
  RingHom.ker (chartMap P u)

instance chartIdeal.isPrime (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartIdeal P u).IsPrime :=
  RingHom.ker_isPrime _

end Chart

def MChartDehomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
    ∀ (f : MRing ι F) (b : K → ℕ), IsMultiHomog f b →
      chartMap P u f = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartHomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (u : ∀ k, ι k) (p : MRing ι F), ∃ (b : K → ℕ) (h : MRing ι F), IsMultiHomog h b ∧
      ∀ (P : Ideal (MRing ι F)) [P.IsPrime], (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
        chartMap P u p = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P h) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartTrdeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime], IsMultiHomogIdeal P →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
      Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P)

def MChartLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime], P ≤ W →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) →
      ringKrullDim (degZeroLoc P {W}) =
        ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).height

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
