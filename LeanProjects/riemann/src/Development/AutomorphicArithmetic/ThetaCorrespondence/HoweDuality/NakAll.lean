import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadFin
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Nak
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.SlotBasic
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nakAll :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel K : ∀ i, Submodule ℂ (M i)), (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (K i)) → (∀ i, Rad (Op i) (Rel i) (K i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N ⊔ (⨆ i, part M₀ i (K i)) = ⊤ → N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op Rel K hRel hK hRad N hN hOp hsup
  have key : ∀ S : Finset ι, N ⊔ (⨆ i ∈ S, part M₀ i (K i)) = ⊤ → N = ⊤ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro h; simpa using h
    | insert i S hi ih =>
      intro h
      apply ih
      refine UpperTheory.Lit.HoweDuality.nak (fun r : M₀ × (∀ j, M j) => intersection_update_fsHerm_neg_one i r) (Op i) (Rel i) (K i) _
        (UpperTheory.Lit.HoweDuality.slotFacts i).1 (fun g hg => ⟨factorOp i g, (UpperTheory.Lit.HoweDuality.slotFacts i).2 g, ?_⟩)
        (fun r x hx => Submodule.mem_sup_left (hN i x hx r.1 r.2))
        (UpperTheory.Lit.HoweDuality.radFin _ _ _ (hRel i) (hK i) (hRad i)) ?_
      · have hle : N ⊔ (⨆ l ∈ S, part M₀ l (K l)) ≤
            (N ⊔ (⨆ l ∈ S, part M₀ l (K l))).comap (factorOp i g) := by
          refine sup_le (fun t ht => Submodule.mem_sup_left (hOp i g hg t ht))
            (iSup₂_le fun l hl t ht => Submodule.mem_sup_right ?_)
          have hne : i ≠ l := fun e => hi (e ▸ hl)
          exact (le_iSup₂ (f := fun l (_ : l ∈ S) => part M₀ l (K l)) l hl)
            ((UpperTheory.Lit.HoweDuality.partStable l (K l)).2.2 i hne g t ht)
        exact fun t ht => hle ht
      · rw [Finset.iSup_insert, sup_comm (part M₀ i (K i)), ← sup_assoc] at h
        exact h
  apply key Finset.univ
  simpa using hsup
