import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.NakAll
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.tens :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀] {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i), Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N → (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) → (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) → Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) → (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (LinearMap.ker (p i))) → (∀ i, Rad (Op i) (Rel i) (LinearMap.ker (p i))) → (∀ i, ∀ N : Submodule ℂ (M i), LinearMap.ker (p i) ≤ N → Stable (Op i) N → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) → (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀ hRel hK hRad
    hmax N hN₀ hN hOp₀ hOp
  have stab : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)), (∀ t ∈ N, Φ t ∈ N) →
      (∀ l, ∀ t ∈ part M₀ l (LinearMap.ker (p l)), Φ t ∈ part M₀ l (LinearMap.ker (p l))) →
      ∀ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))),
        Φ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) := by
    intro Φ h1 h2
    have hle : N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) ≤
        (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l)))).comap Φ :=
      sup_le (fun t ht => Submodule.mem_sup_left (h1 t ht))
        (iSup_le fun l t ht => Submodule.mem_sup_right
          ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) l) (h2 l t ht)))
    exact fun t ht => hle ht
  have key := GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules Op₀ Op Rel₀ (fun i => LinearMap.ker (p i)) p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀
    (fun i => ⟨2, fun m C hC h => ?_⟩) hmax (fun i => le_rfl) hK
    (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))))
    (fun x hx y => Submodule.mem_sup_left (hN₀ x hx y))
    (fun i x hx x₀ y => Submodule.mem_sup_right
      ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) i)
        ((le_iSup (fun r : M₀ × ∀ j, M j => (LinearMap.ker (p i)).map (intersection_update_fsHerm_neg_one i r)) (x₀, y))
          (Submodule.mem_map_of_mem hx))))
    (fun g hg => stab _ (hOp₀ g hg) fun l => (partStable l _).1 g)
    (fun i g hg => stab (factorOp i g) (hOp i g hg) fun l => ?_)
  · rcases key with h | h
    · exact Or.inl (nakAll Op Rel (fun i => LinearMap.ker (p i)) hRel hK hRad N hN hOp h)
    · exact Or.inr (le_sup_left.trans h)
  · by_contra hm
    have hm : 2 < m := not_le.1 hm
    have h01 : C ⟨0, by omega⟩ < C ⟨1, by omega⟩ := hC (by simp [Fin.lt_def])
    have h12 : C ⟨1, by omega⟩ < C ⟨2, hm⟩ := hC (by simp [Fin.lt_def])
    have h1 := hmax i _ (h ⟨1, by omega⟩).1 (h ⟨1, by omega⟩).2 h12.ne_top
    exact absurd (h01.trans_le (h1.trans (h ⟨0, by omega⟩).1)) (lt_irrefl _)
  · by_cases hl : i = l
    · subst hl
      exact (partStable i _).2.1 g (hK i g hg)
    · exact (partStable l _).2.2 i hl g
