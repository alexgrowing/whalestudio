import Formalism.GaussValuationBounds.GaussValueContraction.ExponentSumIdentity
import Formalism.GaussValuationBounds.GaussValueContraction.WStepContract
import Formalism.GaussValuationBounds.GaussValueContraction.SigBound
import Formalism.GaussValuationBounds.GaussValueContraction.TruncationExponentBounds
import Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactVariant
import Formalism.GaussValuationBounds.GaussValueContraction.PhiIterXProof
import Formalism.GaussValuationBounds.GaussValueContraction.GaussValueContractionProofFactBis
import Formalism.GaussValuationBounds.GaussValueContraction.KapBoundProof
import Formalism.GaussValuationBounds.GaussValueContraction.GaussMul
import Formalism.GaussValuationBounds.GaussValueContraction.GaussBasic
import Formalism.GaussValuationBounds.GaussValueContraction.LemmaCVal

namespace Formalism.NOK

theorem nok_LemmaCVal : LemmaCVal :=
  lemmaCVal_of gaussValMul minLeGaussValAdd gaussValC gaussValUnit gaussEis_true

theorem nok_all :
    PowContent ∧ SigNum ∧ RelCoeff ∧ RelVanish ∧ Rel1 ∧ Rel2 ∧ PhiIterX ∧ PsIdeal ∧ DelVal ∧
    DSat ∧ DUDeg ∧ LemmaCVal ∧ ExpNonzero ∧ KapBound ∧ WCycle ∧ WThin ∧ WCut ∧ SigBound ∧
    ETotal ∧ CjExist ∧ GapPure1 ∧ GapPure2 ∧ ExponentSumIdentity ∧ SlopeNum :=
  ⟨powMemSpanPow, truncationExponentBounds, scaledPowMemSpan, powMemSpanOfLe, gaussValueContraction_proof_fact_form, gaussValueContraction_proof_fact_variant,
    phiIterX_proof, psIdeal_proof, delVal_proof, dSat_proof, dUDeg_proof, nok_LemmaCVal,
    expNonzero_proof, kapBound_proof, wCycle_proof, wThin_proof, wCut_proof, sigBound_proof,
    eTotal_proof, cjExist_proof, gaussValueContraction_proof_fact_bis, gaussValueContraction_proof_fact_alt, exponentSumIdentity, slopeNum_proof⟩

theorem nok_gauss : GaussMul ∧ GaussAdd ∧ GaussC ∧ GaussUnit ∧ GaussEis :=
  ⟨gaussValMul, minLeGaussValAdd, gaussValC, gaussValUnit, gaussEis_true⟩

theorem nok_rel_base {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (B : Formalism.WachCohomologyFacts.Base O A) (hℓ : 3 ≤ B.ℓ) (E M j r : ℕ) (hj : 1 ≤ j) :
    (B.ℓ : A) ^ sigNOK B.ℓ E M j * ((⇑B.φ)^[j] B.X) ^ r ∈
      Ideal.span {(B.ℓ : A) ^ (r + padicValNat B.ℓ r.factorial),
        B.X ^ M * ∏ s ∈ Finset.range j, B.p s ^ E} := by
  have : Fact B.ℓ.Prime := ⟨B.hℓ⟩
  obtain ⟨v, -, hv⟩ := phiIterX_proof O A B j
  rw [hv]
  exact scaledPowMemSpan A B.ℓ hℓ B.X v B.p E M j hj (psIdeal_proof O A B (j - 1)) r

theorem nok_exponent (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j ell : ℕ) (hj : 1 ≤ j) (r κ R K : ℝ)
    (hr0 : 0 ≤ r) (hr : r ≤ R) (hκ : κ ≤ K) :
    let σ : ℝ := sigNOK ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j
    2 * r + 4 * σ + max r (2 * (2 * σ + r + 2 * g * ell)) + 2 * κ ≤
      4 * R + 8 * (3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 7 / 4) +
        4 * g * ell + 2 * K := by
  intro σ
  have hs := sigBound_proof ℓ hℓ g h j hj
  rw [eTotal_proof r σ κ g ell hr0 (by positivity) (by positivity) (by positivity)]
  have : (0:ℝ) ≤ 4 * g * ell := by positivity
  linarith

end Formalism.NOK
