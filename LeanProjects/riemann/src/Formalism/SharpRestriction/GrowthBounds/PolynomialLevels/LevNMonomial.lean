import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.TlNonempty

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem levN_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levN Fr p hk nL (F + G) = levN Fr p hk nL F + levN Fr p hk nL G := by
  unfold levN
  exact sumSupp_add (fun mo => (monomial (R := KK O) (noMon Fr p hk nL mo)).toAddMonoidHom) F G

theorem levN_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levN Fr p hk nL (monomial mo c) = monomial (noMon Fr p hk nL mo) c := by
  unfold levN
  by_cases h : c = 0
  · subst h; simp
  · rw [support_monomial, if_neg h, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def psiExp (a : TL J nL r × Fin K →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  a.sum fun v e => Finsupp.single (noVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * e)

def Psi : MvPolynomial (TL J nL r × Fin K) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (noVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

theorem Psi_monomial (a : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    Psi (O := O) Fr p hk nL (monomial a c) = monomial (psiExp Fr p hk nL a) c := by
  unfold Psi psiExp
  rw [aeval_monomial, monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← pow_mul, X_pow_eq_monomial]

variable {Fr nL}

theorem noVar_inj {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) {x x' : TL J nL r} {b b' : Fin K}
    (h : noVar Fr hk nL x b = noVar Fr hk nL x' b') : x = x' ∧ b = b' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [noVar] at h1 h2
  exact ⟨dg_inj hV hr hJ hnL h1, Fin.natAdd_injective K r (Fin.cast_injective _ h2)⟩

theorem noMon_psiExp {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin K →₀ ℕ) :
    noMon Fr p hk nL (psiExp Fr p hk nL a) = a := by
  ext ⟨x, b⟩
  have hP : 0 < lowP Fr p x := pow_pos hp _
  have h1 : psiExp Fr p hk nL a (noVar Fr hk nL x b) = lowP Fr p x * a (x, b) := by
    unfold psiExp
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single (x, b)]
    · rw [Finsupp.single_eq_same]
    · intro v _ hv
      rw [Finsupp.single_apply, if_neg]
      intro h
      obtain ⟨e1, e2⟩ := noVar_inj hk hV hr hJ hnL h
      exact hv (Prod.ext e1 e2)
    · intro _
      rw [mul_zero, Finsupp.single_zero, Finsupp.zero_apply]
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [h1, Nat.mul_div_cancel_left _ hP]

theorem levN_Psi {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (H : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    levN Fr p hk nL (Psi (O := O) Fr p hk nL H) = H := by
  induction H using MvPolynomial.induction_on' with
  | monomial a c => rw [Psi_monomial, levN_monomial, noMon_psiExp p hk hp hV hr hJ hnL]
  | add F G hF hG => rw [map_add, levN_add, hF, hG]

end Lev

theorem seg_Psi (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (i : ℤ)
    (hsurj : ∀ x ∈ Fr.letters i, ¬ Fr.IsW i x → ∃ t : TL J nL r, segZ t.1 = i ∧ posTL Fr t = x)
    (A : MvPolynomial (ℤ × Fin K) O) (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) :
    MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (phSeg O K p Fr i (nmEmb O r K A))) =
      Psi (O := O) Fr p hk nL (Rn Fr nL A) := by
  have hr : 1 ≤ r := NeZero.one_le
  let f₁ : MvPolynomial (ℤ × Fin K) O →+* MvPolynomial (TV n' (m + 1)) (KK O) :=
    (MvPolynomial.map (algebraMap O (KK O))).comp ((rename (castV hk) : _ →ₐ[O] _).toRingHom.comp
      ((phSeg O K p Fr i).toRingHom.comp (nmEmb O r K).toRingHom))
  let f₂ : MvPolynomial (ℤ × Fin K) O →+* MvPolynomial (TV n' (m + 1)) (KK O) :=
    (Psi (O := O) Fr p hk nL).toRingHom.comp
      ((rename (fun v : ℤ × Fin K => (gT Fr nL v.1, v.2)) : _ →ₐ[KK O] _).toRingHom.comp
        (MvPolynomial.map (algebraMap O (KK O))))
  have key : f₁ A = f₂ A := by
    refine hom_congr_vars ?_ ?_ rfl
    · ext c
      simp [f₁, f₂, nmEmb, phSeg, Psi, MvPolynomial.algebraMap_eq]
    · intro v hv _
      have hv' := (mem_supported.1 hA) (Finset.mem_coe.2 hv)
      obtain ⟨t, ht1, ht2⟩ := hsurj v.1 hv'.1 hv'.2
      have hg : gT Fr nL v.1 = t := by
        rw [← ht2]
        exact Function.leftInverse_invFun (dg_posTL_inj hV hr hnL) t
      obtain ⟨x, c⟩ := v
      simp only at hg ht2
      simp only [f₁, f₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nmEmb, phSeg, Psi, rename_X,
        aeval_X, map_pow, map_X, hg]
      simp only [castV, noVar, lowP, ht1, ht2]
  exact key

theorem levN_zNo (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O]
    [IsDomain O] (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J]
    (nL : ZMod J → ℕ) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (hsurj : ∀ i : ℕ, i < Fr.J → ∀ x ∈ Fr.letters i, ¬ Fr.IsW i x →
      ∃ t : TL J nL r, segZ t.1 = (i : ℤ) ∧ posTL Fr t = x)
    (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (hG : ∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) :
    levN Fr p hk nL (zNo p O hk Fr G) = ∏ i ∈ Finset.range Fr.J, Rn Fr nL (G i) := by
  have hr : 1 ≤ r := NeZero.one_le
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : zNo p O hk Fr G = Psi (O := O) Fr p hk nL (∏ i ∈ Finset.range Fr.J, Rn Fr nL (G i)) := by
    unfold zNo
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    exact seg_Psi p O hk Fr L₁ N₁ hV nL hnL (i : ℤ) (hsurj i hi') (G i) (hG i hi')
  rw [h1, levN_Psi p hk hp hV hr hJ hnL]

end Formalism.MainNotions.NormalSetCounting
