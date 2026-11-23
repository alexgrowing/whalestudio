import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGeneratorPreservesForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_generator_preserves_form : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F),
    g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ) →
    (∀ v w : κ ⊕ κ → F, ((g *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ w) ∘ Sum.inr) - ((g *ᵥ w) ∘ Sum.inl) ⬝ᵥ ((g *ᵥ v) ∘ Sum.inr) =
      (v ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) - (w ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inr)) ∧ Function.Surjective fun v : κ ⊕ κ → F => g *ᵥ v := by
  first | exact @GlobalTheory.AdelicSvN.closure_gens_symp | exact GlobalTheory.AdelicSvN.closure_gens_symp | (intros; apply GlobalTheory.AdelicSvN.closure_gens_symp <;> assumption)
