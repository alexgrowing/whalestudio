import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintLevel

theorem finsum_prod_fst {A T : Type} [Finite T] [Nonempty T] (f : A → ℂ) :
    ∑ᶠ x : A × T, f x.1 = (Nat.card T : ℂ) * ∑ᶠ a : A, f a := by
  by_cases hf : (Function.support f).Finite
  · have hg : (Function.support fun x : A × T => f x.1).Finite := by
      refine (hf.prod (Set.finite_univ (α := T))).subset ?_
      intro x hx
      exact ⟨hx, Set.mem_univ _⟩
    rw [finsum_curry _ hg, mul_finsum]
    refine finsum_congr fun a => ?_
    haveI := Fintype.ofFinite T
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : T, f a = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · have hg : ¬ (Function.support fun x : A × T => f x.1).Finite := by
      intro hg
      apply hf
      refine (hg.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, Classical.arbitrary T), ha, rfl⟩
    rw [finsum_of_infinite_support hg, finsum_of_infinite_support hf, mul_zero]

theorem sum_level (H : Type) [Group H] (S L : Subgroup H) (u : H → ℂ) (hLS : L ≤ S) (hS : S ≤ rStab u)
    (hfin : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ p : H ⧸ S, u p.out := by
  have hinv : ∀ g : H, u ((QuotientGroup.mk g : H ⧸ S).out) = u g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul S g
    rw [hk]
    exact hS k.2 g
  have hfst : ∀ q : H ⧸ L, u q.out = u ((Subgroup.quotientEquivProdOfLE hLS q).1.out) := by
    intro q
    have : (Subgroup.quotientEquivProdOfLE hLS q).1 = (QuotientGroup.mk q.out : H ⧸ S) := by
      simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, hinv]
  haveI : Finite (S ⧸ L.subgroupOf S) := Subgroup.index_ne_zero_iff_finite.1 hfin
  rw [finsum_congr hfst, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hLS)
    (f := fun x : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u x.1.out)]
  exact finsum_prod_fst (fun p : H ⧸ S => u p.out)

theorem hint_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hne
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have h1 : L.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, zero_mul]
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, mul_zero]
  rw [sum_level H (rStab u ⊓ K) L u hLS inf_le_left h1, hint, ← hmul]
  push_cast
  have h1' : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1
  field_simp

end GlobalTheory.BCT.HintLevel
