import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def blowUpEval (P : Ideal (MRing ι R)) (u : J → MRing ι R) : MRing (extIdx ι J) R →+* MRing ι R ⧸ P :=
  (Polynomial.evalRingHom 1).comp (aeval (blowUpSubst P u)).toRingHom

variable [DecidableEq K]

def blowUpLocRing (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R)
    (Q : Ideal (MRing (extIdx ι J) R)) : Subring (FractionRing (MRing ι R ⧸ P)) :=
  Subring.closure {z | ∃ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b ∧
    IsMultiHomog G b ∧ G ∉ Q ∧
    z = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)}

def blowUpOverLoc (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Subring (FractionRing (MRing ι R ⧸ P)) :=
  ⨅ (Q : Ideal (MRing (extIdx ι J) R)) (_ : Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
      blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W),
    blowUpLocRing P u Q

omit [DecidableEq K] in

theorem blowUpEval_liftForm (P : Ideal (MRing ι R)) (u : J → MRing ι R) (f : MRing ι R) :
    blowUpEval P u (liftForm f) = Ideal.Quotient.mk P f := by
  show Polynomial.eval 1 (aeval (blowUpSubst P u) (liftForm f)) = _
  rw [aeval_blowUpSubst_liftForm, Polynomial.eval_C]

theorem homLocRing_le_blowUpOverLoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    homLocRing P W ≤ blowUpOverLoc P W u := by
  refine le_iInf₂ fun Q hQ => Subring.closure_le.mpr ?_
  rintro z ⟨b, f, g, hf, hg, hgW, rfl⟩
  refine Subring.subset_closure ⟨liftMDeg b, liftForm f, liftForm g, isMultiHomog_liftForm hf,
    isMultiHomog_liftForm hg, fun h => hgW (hQ.2.2.2.2 h), ?_⟩
  rw [blowUpEval_liftForm, blowUpEval_liftForm]

instance blowUpOverLoc.instAlgebra {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    (P W : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) :
    Algebra (homLocRing P W) (blowUpOverLoc P W u) :=
  (Subring.inclusion (homLocRing_le_blowUpOverLoc P W u)).toAlgebra

end Objects

section Lemmas

def BlowUpLocRingIso.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (J : Type)
    (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (Q : Ideal (MRing (extIdx ι J) R)),
    blowUpOf P u ≤ Q →
    haveI : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
    ∃ φ : homLocRing (blowUpOf P u) Q ≃+* blowUpLocRing P u Q,
      ∀ (b : Option K → ℕ) (F G : MRing (extIdx ι J) R) (hF : IsMultiHomog F b)
        (hG : IsMultiHomog G b) (hGQ : G ∉ Q),
        (φ ⟨_, Subring.subset_closure ⟨b, F, G, hF, hG, hGQ, rfl⟩⟩ : FractionRing (MRing ι R ⧸ P)) =
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G)

def BlowUpOverLocFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      Module.Finite (homLocRing P W) (blowUpOverLoc P W u) ∧
        Module.finrank (homLocRing P W) (blowUpOverLoc P W u) = 1

def BlowUpOverLocMax.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∃ e : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal} ≃ {W' : Ideal (MRing (extIdx ι J) O) //
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W},
        ∀ 𝔫 : {𝔫 : Ideal (blowUpOverLoc P W u) // 𝔫.IsMaximal},
          (∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u (e 𝔫).1,
            letI := (Subring.inclusion h).toAlgebra
            haveI := 𝔫.2.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u (e 𝔫).1) 𝔫.1) ∧
          𝔫.1.inertiaDeg (homLocRing P W) = specialRelDeg (e 𝔫).1

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
