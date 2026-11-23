import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAtStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicitStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitSlashInvariantGamma1InterGStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitEqSumSlashStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isZeroAt_zero_fun (c : OnePoint ℝ) (k : ℤ) : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  simpa using! Filter.zero_zeroAtFilter _

theorem isZeroAt_finset_sum {ι : Type*} (s : Finset ι) (c : OnePoint ℝ) (k : ℤ) (F : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (F i) k) : c.IsZeroAt (∑ i ∈ s, F i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isZeroAt_zero_fun c k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem uOp_cuspForm : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  intro N l q k hN hl hq hqd f
  have hinv : ∀ γ ∈ GlobalTheory.Hk.lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ =>
    SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩
  have hU := GlobalTheory.T.heckeUOperatorExplicit_slash_invariant_gamma1InterGamma0 N l q k (⇑f) hN hl hq hqd hinv
  refine ⟨{ toFun := GlobalTheory.Hk.uOp q ⇑f
            slash_action_eq' := fun A hA => by
              obtain ⟨A, hA, rfl⟩ := hA
              exact hU A hA
            holo' := (GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit q k 1 (⇑f) hq.pos (CuspFormClass.holo f)).1
            zero_at_cusps' := fun {c} hc => by
              rw [GlobalTheory.T.heckeUOperatorExplicit_eq_sum_slash q k (⇑f) hq.pos]
              exact isZeroAt_finset_sum _ c k _ fun j _ =>
                GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt N l k _ hN hl (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.pos) f c hc }, rfl⟩

end GlobalTheory.Hk
