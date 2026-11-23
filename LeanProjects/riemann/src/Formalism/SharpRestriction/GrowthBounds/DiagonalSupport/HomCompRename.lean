import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembAlgF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Comp

variable {R : Type} [CommRing R] {ι κ : Type} {n : ℕ}

theorem coeff_homComp (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R) (a : ι × Fin n →₀ ℕ) :
    (homComp δ F).coeff a = if (∀ i, multideg a i = δ i) then F.coeff a else 0 := by
  classical
  unfold homComp
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  by_cases h : ∀ i, multideg a i = δ i <;> by_cases hc : F.coeff a = 0 <;> simp [h, hc]

theorem homComp_rename (f : κ × Fin n → ι × Fin n) (δ : ι → ℕ) (G : MvPolynomial (κ × Fin n) R) :
    ∃ G' : MvPolynomial (κ × Fin n) R, G'.support ⊆ G.support ∧ rename f G' = homComp δ (rename f G) := by
  classical
  refine ⟨∑ mo ∈ G.support.filter (fun mo => ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i),
    monomial mo (G.coeff mo), ?_, ?_⟩
  · intro mo hmo
    obtain ⟨x, hx, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hmo)
    rw [Finset.mem_singleton.mp (support_monomial_subset h2)]
    exact (Finset.mem_filter.mp hx).1
  · ext a
    rw [coeff_homComp]
    conv_rhs => rw [G.as_sum]
    simp only [map_sum, coeff_sum, rename_monomial, coeff_monomial]
    rw [Finset.sum_filter]
    split_ifs with h
    · apply Finset.sum_congr rfl
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        rw [if_pos hP]
      · simp only [hm, if_false, ite_self]
    · apply Finset.sum_eq_zero
      intro mo _
      by_cases hm : Finsupp.mapDomain f mo = a
      · have hP : ¬ ∀ i, multideg (Finsupp.mapDomain f mo) i = δ i := by rw [hm]; exact h
        simp [hP]
      · simp [hm]

end Comp

section Big

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

private theorem upPl_monomial_eq_monomial_mPl (bp : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    upPl Fr p O hk nL (monomial bp c) = monomial (mPl Fr p hk nL bp) c := by
  rw [show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upPl, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

private theorem upNo_monomial_eq_monomial_mNo (bn : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    upNo Fr p O hk nL (monomial bn c) = monomial (mNo Fr p hk nL bn) c := by
  rw [show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upNo, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

theorem asm_support (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) (mm : TV n' (m + 1) →₀ ℕ)
    (h : mm ∈ (asm Fr p O hk nL rho A N).support) :
    ∃ bp ∈ A.support, ∃ bn ∈ N.support, mm = bigM Fr p hk nL rho bp bn := by
  classical
  have e : asm Fr p O hk nL rho A N = ∑ bp ∈ A.support, ∑ bn ∈ N.support,
      monomial (bigM Fr p hk nL rho bp bn) (A.coeff bp * N.coeff bn) := by
    conv_lhs => rw [asm, A.as_sum, N.as_sum]
    simp only [map_sum, upPl_monomial_eq_monomial_mPl, upNo_monomial_eq_monomial_mNo, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bp _
    apply Finset.sum_congr rfl
    intro bn _
    rw [monomial_mul, monomial_mul, one_mul, bigM_eq]
  rw [e] at h
  obtain ⟨bp, hbp, h2⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h)
  obtain ⟨bn, hbn, h3⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum h2)
  exact ⟨bp, hbp, bn, hbn, Finset.mem_singleton.mp (support_monomial_subset h3)⟩

theorem bigM_off (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (s : Fin n') (hs : s ∉ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)) (c : Fin (m + 1)) :
    bigM Fr p hk nL rho bp bn (s, c) = 0 := by
  apply bigM_notin
  rintro ⟨v, hv⟩
  exact hs ⟨v.1, congrArg Prod.fst hv⟩

theorem multideg_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (hsurj : ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s)
    (htop : ∀ x : TL J nL r, posOf n' (posTL Fr x) ∈ Fr.TT)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0)
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) (hB : BlockOK Fr p nL d rho dPl dNo)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) (h1 : ∀ x, multideg bp x = dPl x)
    (h2 : ∀ x, multideg bn x = dNo x) (s : Fin n') : multideg (bigM Fr p hk nL rho bp bn) s = d s := by
  by_cases hs : s ∈ Set.range fun x : TL J nL r => posOf n' (posTL Fr x)
  · obtain ⟨x, rfl⟩ := hs
    have hsc : multideg (bigM Fr p hk nL rho bp bn) (posOf n' (posTL Fr x)) =
        ∑ a : Fin r, bigM Fr p hk nL rho bp bn (plVar Fr hk nL x a) +
          ∑ b : Fin K, bigM Fr p hk nL rho bp bn (noVar Fr hk nL x b) := by
      unfold multideg
      rw [← Equiv.sum_comp (finCongr hk.symm) (fun c => bigM Fr p hk nL rho bp bn (posOf n' (posTL Fr x), c)),
        Fin.sum_univ_add]
      rfl
    rw [hsc]
    simp only [bigM_pl hinj, bigM_no hinj, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hB.2 x, ← h1 x, ← h2 x, Fin.sum_univ_add (fun c => rho (x, c))]
    unfold multideg
    ring
  · have hT : s ∉ Fr.TT := fun hT => hs (hsurj s hT)
    rw [hd s hT]
    unfold multideg
    exact Finset.sum_eq_zero (fun c _ => bigM_off Fr p hk nL htop rho bp bn s hs c)

end Big

end Formalism.MainNotions.Proposition5Numerics
