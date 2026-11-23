import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.TlNonempty
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TensZeroRight

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section LevP

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

def psiExpP (a : TL J nL r × Fin r →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  a.sum fun v e => Finsupp.single (plVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * e)

def PsiP : MvPolynomial (TL J nL r × Fin r) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (plVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

theorem PsiP_monomial (a : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    PsiP (O := O) Fr p hk nL (monomial a c) = monomial (psiExpP Fr p hk nL a) c := by
  unfold PsiP psiExpP
  rw [aeval_monomial, monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← pow_mul, X_pow_eq_monomial]

variable {Fr nL}

theorem plVar_inj {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) {x x' : TL J nL r} {a a' : Fin r}
    (h : plVar Fr hk nL x a = plVar Fr hk nL x' a') : x = x' ∧ a = a' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Formalism.MainNotions.TestSideWords.plVar] at h1 h2
  exact ⟨dg_inj hV hr hJ hnL h1, Fin.castAdd_injective r K (Fin.cast_injective _ h2)⟩

theorem psiExpP_apply {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin r →₀ ℕ) (x : TL J nL r) (a' : Fin r) :
    psiExpP Fr p hk nL a (plVar Fr hk nL x a') = lowP Fr p x * a (x, a') := by
  unfold psiExpP
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single (x, a')]
  · rw [Finsupp.single_eq_same]
  · intro v _ hv
    rw [Finsupp.single_apply, if_neg]
    intro h
    obtain ⟨e1, e2⟩ := plVar_inj hk hV hr hJ hnL h
    exact hv (Prod.ext e1 e2)
  · intro _
    rw [mul_zero, Finsupp.single_zero, Finsupp.zero_apply]

theorem plMon_psiExpP_add {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin r →₀ ℕ) (c : TV n' (m + 1) →₀ ℕ) :
    plMon Fr p hk nL (psiExpP Fr p hk nL a + c) = plMon Fr p hk nL c + a := by
  ext ⟨x, a'⟩
  have hP : 0 < lowP Fr p x := pow_pos hp _
  simp only [plMon, Finsupp.coe_equivFunOnFinite_symm, Finsupp.add_apply]
  rw [psiExpP_apply p hk hV hr hJ hnL, Nat.mul_add_div hP, add_comm]

theorem levelAtPrime_character_mul {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (H : MvPolynomial (TL J nL r × Fin r) (KK O))
    (c : TV n' (m + 1) →₀ ℕ) :
    levP Fr p hk nL (PsiP (O := O) Fr p hk nL H * monomial c 1) = monomial (plMon Fr p hk nL c) 1 * H := by
  induction H using MvPolynomial.induction_on' with
  | monomial a k =>
    rw [PsiP_monomial, monomial_mul, T5.monomialSubstitution_monomial, plMon_psiExpP_add p hk hp hV hr hJ hnL, monomial_mul, mul_one,
      one_mul]
  | add F G hF hG => rw [map_add, add_mul, T5.monomialSubstitution_add, hF, hG, mul_add]

end LevP

end Formalism.MainNotions.NormalSetCounting
