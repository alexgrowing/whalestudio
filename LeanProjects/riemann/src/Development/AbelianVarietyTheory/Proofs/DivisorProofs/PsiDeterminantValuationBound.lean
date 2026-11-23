import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantEigenPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantElementProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFunctionOnMonoidLinearStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem log_val_lead_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ τ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (N : ℕ) (Δ : RL p O Λ) (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ → HasOrders C ε N Δ a c → Real.log (v (c τ)) = N * κ₀ + ∑ᶠ σ, (a σ : ℝ) * κ σ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ τ
  classical
  haveI : Finite (Λ →+* O) := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  letI : Fintype (Λ →+* O) := Fintype.ofFinite _
  let S : Set (Option (Λ →+* O) → ℕ) := {x | ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C),
    IsDetElt ε ψ (x none) Δ ∧ HasOrders C ε (x none) Δ (fun σ => x (some σ)) c}
  let F : (Option (Λ →+* O) → ℕ) → ℝ := fun x =>
    if h : x ∈ S then Real.log (v (Classical.choose (Classical.choose_spec h) τ)) else 0
  have hF : ∀ x (h : x ∈ S) (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ (x none) Δ →
      HasOrders C ε (x none) Δ (fun σ => x (some σ)) c → F x = Real.log (v (c τ)) := by
    intro x h Δ c h1 h2
    simp only [F, dif_pos h]
    obtain ⟨h1', h2'⟩ := Classical.choose_spec (Classical.choose_spec h)
    rw [GlobalTheory.T.psi_determinant_eigen_property p C v O hv ε hε Λ ψ hψ (x none) _ Δ _ _ c h1' h1 h2' h2 τ]
  obtain ⟨f, hf, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
  have hne : ∀ N (Δ : RL p O Λ) a (c : (Λ →+* O) → C), HasOrders C ε N Δ a c →
      ((v (c τ) : NNReal) : ℝ) ≠ 0 := fun N Δ a c h =>
    NNReal.coe_ne_zero.2 ((Valuation.ne_zero_iff v).2 (h τ f hf).2.1)
  obtain ⟨κ', hκ'⟩ := GlobalTheory.T.additive_function_on_monoid_linear (Option (Λ →+* O)) S F (by
    rintro x ⟨Δ, c, h1, h2⟩ y ⟨Δ', c', h1', h2'⟩
    obtain ⟨k1, k2⟩ := GlobalTheory.T.determinant_element_product p O C ε Λ ψ _ _ Δ Δ' _ _ c c' h1 h1' h2 h2'
    have hxy : x + y ∈ S := ⟨Δ * Δ', c * c', k1, k2⟩
    refine ⟨hxy, ?_⟩
    rw [hF _ hxy _ _ k1 k2, hF x ⟨Δ, c, h1, h2⟩ _ _ h1 h2, hF y ⟨Δ', c', h1', h2'⟩ _ _ h1' h2',
      Pi.mul_apply, map_mul, NNReal.coe_mul, Real.log_mul (hne _ _ _ _ h2) (hne _ _ _ _ h2')])
  refine ⟨κ' none, fun σ => κ' (some σ), ?_⟩
  intro N Δ a c h1 h2
  let x : Option (Λ →+* O) → ℕ := fun o => o.elim N a
  have hx : x ∈ S := ⟨Δ, c, h1, h2⟩
  rw [← hF x hx Δ c h1 h2, hκ' x hx, Fintype.sum_option, finsum_eq_sum_of_fintype]
  rfl

end GlobalTheory.DetInv
