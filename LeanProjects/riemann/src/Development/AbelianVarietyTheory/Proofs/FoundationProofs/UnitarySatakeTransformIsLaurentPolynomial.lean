import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame

noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}

open Classical in

def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
