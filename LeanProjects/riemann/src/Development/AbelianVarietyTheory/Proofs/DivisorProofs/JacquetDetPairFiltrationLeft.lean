import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubSmulMemOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCellFunctorEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCellFunctorApplyStatement

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.DetProdCells

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]

theorem cell_first_step (χ₁ χ₂ : kˣ →* ℂˣ) (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ)
    (bb : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v)))) (hbb : bb = cellFirst u v)
    (σ : Representation ℂ (Levi k (Two (Fin 1) (Fin (u + v)))) Y)
    (hσ : ∀ (f : ∀ i, (Σ j, Fin (bb.1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i)
      (g : ∀ j, (Σ i, Fin (bb.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j),
      Nonempty (σ.Equiv (cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
        (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)))) :
    Nonempty (Representation.Equiv (σ.comp (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom)
      (extTensor (detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2)))
        (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)))) := by
  subst hbb
  obtain ⟨f, g, ⟨ψ⟩⟩ := GlobalTheory.T.first_cell_functor_equiv χ₁ χ₂ h₁ h₂ u v
  obtain ⟨φ⟩ := hσ f g
  exact ⟨(compEquiv' φ (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom).trans ψ⟩

theorem cell_other_scalar (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (bb : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v)))) (hbb : bb ≠ cellFirst u v) (ϖ : kˣ)
    (σ : Representation ℂ (Levi k (Two (Fin 1) (Fin (u + v)))) Y)
    (hσ : ∀ (f : ∀ i, (Σ j, Fin (bb.1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i)
      (g : ∀ j, (Σ i, Fin (bb.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j),
      Nonempty (σ.Equiv (cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
        (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)))) :
    ∀ x, σ (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) x =
      (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • x := by
  obtain ⟨hv, rfl⟩ := (eq_cellFirst_or u v bb).resolve_left hbb
  obtain ⟨f, g, hz⟩ := GlobalTheory.T.second_cell_functor_apply χ₁ χ₂ u v hv ϖ
  obtain ⟨φ⟩ := hσ f g
  exact smul_of_equiv φ _ _ hz

end Cells

set_option maxHeartbeats 1000000 in

theorem jac_prod_det_filtration : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (e : Fin 1 ⊕ Fin (u + v) ≃ Fin (u + 1 + v)) (ϖ : kˣ), ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)))), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N, Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) (χ₁ * absPow k (-(u : ℂ) / 2))) (prod₂ (detRep (Fin u) (χ₁ * absPow k (1 / 2))) (detRep (Fin v) χ₂)))) ∧ ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, jac₂ e (prod₂ (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) w - (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w ∈ (S t.castSucc).toSubmodule := by
  intro k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v e ϖ
  have hJ : JacquetOfInducedFiltration k := hG k
  have H := hJ Bool Bool (Fin (u + 1 + v)) (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v)))
    (two (stdSum (rfl : u + 1 + v = u + 1 + v))) (two e)
  obtain ⟨N, H⟩ := H
  obtain ⟨b, hb⟩ := H
  have hc : Continuous (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  have HS := hb (TensorProduct ℂ ℂ ℂ) ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom) hsm
  obtain ⟨S, hmono, h0, htop, hS⟩ := HS
  have ht₀ : b (b.symm (cellFirst u v)) = cellFirst u v := b.apply_symm_apply _
  exact ⟨N, assemble _ (leviTwo k (Fin 1) (Fin (u + v))).toMonoidHom S hmono h0 htop _
    (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ)
    (b.symm (cellFirst u v)) (cell_first_step χ₁ χ₂ h₁ h₂ u v _ ht₀ _ (hS _))
    (fun t ht => cell_other_scalar χ₁ χ₂ u v (b t) (fun h => ht (b.injective (h.trans ht₀.symm))) ϖ _ (hS t))⟩

end GlobalTheory.DetProdCells
