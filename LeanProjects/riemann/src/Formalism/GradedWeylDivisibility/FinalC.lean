import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.MinorExpLt
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColLexInitMinor
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColumnLexBideterminant
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTPeel
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSYTExists
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.CompDeg
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadComp
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDecomp
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelHomog
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelLead
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.EvalDeg
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.PeelDegBound
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TwoColumn
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LeadInterlaced
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SMSAssembly
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.StandardMonomialSpanOf

namespace Formalism.GradedWeylDivisibility

theorem minorExpLt : MinorExpLt := minorExponentLt
theorem colLexInitMinor : ColLexInitMinor := colLexInitMinor_of minorExpLt
theorem column_lex_bideterminant : ColumnLexBideterminant := columnLexBideterminant_of_initialMinor colLexInitMinor
theorem colSums : ColSums := columnSums_holds
theorem sSYTPeel : SSYTPeel := semistandardPeel
theorem sSYTExists : SSYTExists := sSYTExists_of sSYTPeel
theorem compDeg : CompDeg := componentDegree
theorem leadComp : LeadComp := leadingComponent
theorem peelDecomp : PeelDecomp := peelDecomposition
theorem peelHomog : PeelHomog := sliceHomogeneous
theorem peelLead : PeelLead := sliceLeading
theorem evalDeg : EvalDeg := evalDegree
theorem peelDegBound : PeelDegBound := peelDegBound_of evalDeg
theorem twoColumn : TwoColumn := twoColumn_of peelDecomp peelHomog peelLead peelDegBound
theorem leadInterlaced : LeadInterlaced := leadInterlaced_of compDeg leadComp twoColumn
theorem standardMonomialSpanDomain : StandardMonomialSpanDomain :=
  semistandard_module_assembly column_lex_bideterminant colSums sSYTExists leadInterlaced

theorem standardMonomialSpan : StandardMonomialSpan :=
  standardMonomialSpanOf standardMonomialSpanDomain

private theorem bidet_rowPart_lemma {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) (k : ℕ) :
    ∀ (s : Finset (Fin K)) (m : Fin r × Fin n →₀ ℕ),
      m ∈ (∏ j ∈ s, initMinor ℤ (I j) (hsz j)).support → rowPart k m ≤ ∑ j ∈ s, min k (sz j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    simp only [Finset.prod_empty] at hm
    have hm0 : m = 0 := by
      by_contra h
      apply (MvPolynomial.mem_support_iff.mp hm)
      rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)]
    subst hm0
    simp [rowPart_zero]
  | @insert j s hj ih =>
    intro m hm
    rw [Finset.prod_insert hj] at hm
    obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
    rw [rowPart_add, Finset.sum_insert hj]
    exact Nat.add_le_add ((initMinor_support (I j) (hsz j) m1 hm1).1 k) (ih m2 hm2)

private theorem sum_rowNu_lemma_2 {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ j, sz j ≤ n) (hnr : n ≤ r)
    (k : ℕ) :
    ∑ j : Fin K, min k (sz j) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) (shapeDeg (n := n) sz) a := by
  classical
  have h1 : ∀ a : Fin r, rowNu (r := r) (shapeDeg (n := n) sz) a =
      ∑ j : Fin K, if a.val < sz j then 1 else 0 := by
    intro a
    unfold rowNu
    split_ifs with h
    · unfold shapeDeg
      rw [Finset.card_filter]
    · symm
      apply Finset.sum_eq_zero
      intro j _
      have := hsz j
      exact if_neg (by omega)
  have h2 : ∀ j : Fin K, min k (sz j) = ∑ a : Fin r with a.val < k, if a.val < sz j then 1 else 0 := by
    intro j
    have hj : sz j ≤ r := (hsz j).trans hnr
    rw [← Finset.card_filter, Finset.filter_filter]
    have hset : (Finset.univ.filter fun a : Fin r => a.val < k ∧ a.val < sz j).map Fin.valEmbedding =
        Finset.range (min k (sz j)) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        omega
      · intro hx
        exact ⟨⟨x, by omega⟩, by simp only; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hset, Finset.card_range]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  exact le_of_eq (Finset.sum_congr rfl (fun j _ => h2 j))

theorem dualWeylDominanceZ :
    ∀ (r n : ℕ) (ν : Fin n → ℕ), n ≤ r → Antitone ν → ∀ f ∈ dualWeyl ℤ r n ν, ∀ m ∈ f.support,
      (∀ k : ℕ, (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a) ∧
      ∑ a : Fin r, rowDeg m a = ∑ a : Fin r, rowNu (r := r) ν a := by
  intro r n ν hnr hν f hf m hm
  have hcol := colSums ℤ r n ν f hf m hm
  refine ⟨fun k => ?_, ?_⟩
  · rw [standardMonomialSpan r n ν hν] at hf
    clear hcol
    show rowPart k m ≤ _
    induction hf using Submodule.span_induction generalizing m with
    | mem x hx =>
      obtain ⟨K, sz, hsz, I, hν', rfl⟩ := hx
      subst hν'
      exact (bidet_rowPart_lemma sz hsz I k Finset.univ m hm).trans (sum_rowNu_lemma_2 sz hsz hnr k)
    | zero => simp at hm
    | add x y _ _ ihx ihy =>
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · exact ihx m h
      · exact ihy m h
    | smul a x _ ihx =>
      exact ihx m (MvPolynomial.support_smul hm)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnr
    have hL : ∑ a : Fin (n + d), rowDeg m a = ∑ s : Fin n, ν s := by
      unfold rowDeg
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun s _ => hcol s)
    rw [hL, Fin.sum_univ_add]
    simp [rowNu]

end Formalism.GradedWeylDivisibility
