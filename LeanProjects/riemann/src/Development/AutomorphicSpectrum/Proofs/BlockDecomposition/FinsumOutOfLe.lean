import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintLevel

theorem finsum_out_of_le {H : Type} [Group H] {L S : Subgroup H} (u : H → ℂ) (hLS : L ≤ S)
    (hS : S ≤ rStab u) (hm : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ c : H ⧸ S, u c.out := by
  have hm' : Nat.card (S ⧸ L.subgroupOf S) ≠ 0 := hm
  haveI : Finite (S ⧸ L.subgroupOf S) := Nat.finite_of_card_ne_zero hm'
  let e := Subgroup.quotientEquivProdOfLE hLS
  have hfst : ∀ q : H ⧸ L, (e q).1 = ((q.out : H) : H ⧸ S) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (e (g : H ⧸ L)).1 = (g : H ⧸ S) := rfl
    rw [h1]
    exact QuotientGroup.eq.2 (hLS (QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : H ⧸ L)).symm))
  have hg : ∀ q : H ⧸ L, u q.out = u (e q).1.out := by
    intro q
    rw [hfst q]
    have hk : (((q.out : H) : H ⧸ S).out)⁻¹ * q.out ∈ S :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' ((q.out : H) : H ⧸ S))
    have := hS hk (((q.out : H) : H ⧸ S).out)
    simpa using this
  have hcomp : ∑ᶠ q : H ⧸ L, u q.out =
      ∑ᶠ p : (H ⧸ S) × (S ⧸ L.subgroupOf S), u p.1.out := by
    rw [← finsum_comp_equiv e]
    exact finsum_congr hg
  rw [hcomp]
  by_cases hfin : (Function.support fun c : H ⧸ S => u c.out).Finite
  · have hsupp : (Function.support fun p : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u p.1.out).Finite := by
      refine (hfin.prod (Set.finite_univ (α := S ⧸ L.subgroupOf S))).subset ?_
      intro p hp
      exact ⟨hp, Set.mem_univ _⟩
    rw [finsum_curry _ hsupp]
    have hin : ∀ c : H ⧸ S, ∑ᶠ _ : S ⧸ L.subgroupOf S, u c.out = ((L.relIndex S : ℕ) : ℂ) * u c.out := by
      intro c
      haveI := Fintype.ofFinite (S ⧸ L.subgroupOf S)
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card]
      rfl
    simp only [hin]
    rw [mul_finsum]
  · have h0 : ∑ᶠ c : H ⧸ S, u c.out = 0 := finsum_of_infinite_support hfin
    rw [h0, mul_zero]
    refine finsum_of_infinite_support fun hsupp => hfin ?_
    refine (hsupp.image Prod.fst).subset ?_
    intro c hc
    exact ⟨(c, ((1 : S) : S ⧸ L.subgroupOf S)), hc, rfl⟩

theorem hint_eq_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hfin
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have hm : L.relIndex (rStab u ⊓ K) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  rw [finsum_out_of_le u hLS inf_le_left hm, ← hmul, hint]
  have hmC : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [Nat.cast_mul, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.HintLevel
