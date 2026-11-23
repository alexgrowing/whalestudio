import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsContractRelDimLe
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContracted
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

namespace ContractRelDimLe

section Chain

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem ringKrullDim_killIdeal_add_card_le {Q : Ideal (MRing ι F)} [Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q)
    (T : Finset K) :
    ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
      ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  induction T using Finset.induction_on with
  | empty =>
    have : killIdeal Q (∅ : Finset K) = Q := by
      ext q
      simp [killIdeal, killBlocks_empty]
    rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
  | insert k T hk ih =>
    have : (killIdeal Q T).IsPrime := Ideal.comap_isPrime _ _
    have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
      (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
      (by
        change killBlocks T (X ⟨k, i k⟩) ∉ Q
        rw [killBlocks_X, if_neg hk]
        exact hi k)
      (by
        change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
        rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
        exact Q.zero_mem)
    calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
        = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
          rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
            add_comm (1 : WithBot ℕ∞)]
      _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
      _ ≤ _ := ih

end Chain

section Contract

variable {K K' : Type*} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K'] {F : Type*}
  [Field F] (j : K ↪ K') (ι' : K' → Type*)

omit [DecidableEq K] in

theorem killBlocks_compl_rename :
    (killBlocks (ι := ι') (F := F) (Finset.univ.map j)ᶜ).comp (rename (blockIncl j ι')) =
      rename (blockIncl j ι') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X, blockIncl]

omit [DecidableEq K] in

theorem exists_rename_eq_killBlocks_compl (x : MRing ι' F) :
    ∃ a : MRing (fun k => ι' (j k)) F,
      rename (blockIncl j ι') a = killBlocks (Finset.univ.map j)ᶜ x := by
  induction x using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [killBlocks]⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p v hp =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨k', i⟩ := v
    rw [map_mul, killBlocks_X, ← ha]
    by_cases h : k' ∈ (Finset.univ.map j)ᶜ
    · exact ⟨0, by rw [if_pos h, mul_zero, map_zero]⟩
    · rw [if_neg h]
      simp only [Finset.mem_compl, Finset.mem_map, Finset.mem_univ, true_and, not_not] at h
      obtain ⟨k, rfl⟩ := h
      exact ⟨a * X ⟨k, i⟩, by rw [map_mul, rename_X]; rfl⟩

theorem ringKrullDim_contract_eq_killIdeal (P' : Ideal (MRing ι' F)) :
    ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') =
      ringKrullDim (MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ) := by
  set f : MRing (fun k => ι' (j k)) F →+* MRing ι' F ⧸ killIdeal P' (Finset.univ.map j)ᶜ :=
    (Ideal.Quotient.mk _).comp (rename (blockIncl j ι')).toRingHom
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_rename_eq_killBlocks_compl j ι' (F := F) x
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = _
    rw [Ideal.Quotient.eq, ha]
    change killBlocks _ (killBlocks _ x - x) ∈ P'
    rw [map_sub, ← AlgHom.comp_apply, killBlocks_comp le_rfl, sub_self]
    exact P'.zero_mem
  have hker : RingHom.ker f = contractPrime j P' := by
    ext a
    change Ideal.Quotient.mk _ (rename (blockIncl j ι') a) = 0 ↔ rename (blockIncl j ι') a ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change killBlocks _ (rename (blockIncl j ι') a) ∈ P' ↔ _
    rw [← AlgHom.comp_apply, killBlocks_compl_rename]
  rw [← hker]
  exact ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)

end Contract

theorem proof : ContractRelDimLe.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP'
  have := hP'.isPrime
  have hstab : ∀ (T : Finset K') (q : MRing ι' F), q ∈ P' → killBlocks T q ∈ P' :=
    fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq hstab hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (Q := contractPrime j P')
    (contractPrime_killStable j ι' hP'.multiHomog) (contractPrime_isRelevant j ι' hP'.relevant)
  have hchain := ringKrullDim_killIdeal_add_card_le hstab hP'.relevant (Finset.univ.map j)ᶜ
  rw [← ringKrullDim_contract_eq_killIdeal, hD, hD', ← Nat.cast_add] at hchain
  have hle : D + ((Finset.univ.map j)ᶜ).card ≤ D' := by exact_mod_cast hchain
  have hcard : ((Finset.univ.map j)ᶜ).card + Fintype.card K = Fintype.card K' := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ]
    have := Fintype.card_le_of_embedding j
    omega
  rw [relDim_eq_int hD, relDim_eq_int hD']
  exact WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr (by omega))

end ContractRelDimLe

end

end GroundTheory.Heights₂.Heights.FieldNumbers
