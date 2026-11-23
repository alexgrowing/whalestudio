import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTwoBlockEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorScalarUniformizerStatement
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section
namespace GlobalTheory.CellRS

theorem cellLemma : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 0 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j),
      Nonempty (Representation.Equiv ((cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
          (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)).comp
            (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom)
        (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2)))))
          (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2))))) :=
  GlobalTheory.T.cell_functor_two_block_equiv

theorem scalarLemma : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ)
    (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1))), b.1 false true = 1 →
    ∀ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin u) (Fin (v + 1)) i)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin (u + v)) (Fin 1) j) (ϖ : kˣ) w,
      cellFunctor f g ((extTensor (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)).comp
          (leviTwo k (Fin u) (Fin (v + 1))).symm.toMonoidHom)
        (leviTwo k (Fin (u + v)) (Fin 1) (1, GeneralLinearGroup.scalar (Fin 1) ϖ)) w =
        (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w :=
  GlobalTheory.T.cell_functor_scalar_uniformizer

theorem step_scalar {G V Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G V) (B A : Subrepresentation ρ) (τ : Representation ℂ G Y)
    (Ψ : (subQuot B A).Equiv τ) (z : G) (c : ℂ) (hτ : ∀ y, τ z y = c • y)
    (w : V) (hw : w ∈ B.toSubmodule) : ρ z w - c • w ∈ A.toSubmodule := by
  have hZ : ∀ y, subQuot B A z y = c • y := by
    intro y
    apply Ψ.toLinearEquiv.injective
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ Ψ.toIntertwiningMap z y
    rw [Representation.Equiv.toLinearEquiv_apply, h1, hτ, map_smul, Representation.Equiv.toLinearEquiv_apply]
  have hq := hZ (Submodule.Quotient.mk ⟨w, hw⟩)
  have e2 : subQuot B A z (Submodule.Quotient.mk ⟨w, hw⟩) =
      Submodule.Quotient.mk ⟨ρ z w, B.apply_mem_toSubmodule z hw⟩ := rfl
  rw [e2, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hq
  simpa using hq

theorem isSmooth_rhoM {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ₁ χ₂ : kˣ →* ℂˣ} (h₁ : IsSmoothChar χ₁) (h₂ : IsSmoothChar χ₂) (u v : ℕ) :
    IsSmooth ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp
          (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom) := by
  refine isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
    ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ ?_
  exact (continuous_apply false).prodMk (continuous_apply true)
end GlobalTheory.CellRS

namespace GlobalTheory.CellRS

theorem card_two_false (a b : Type) [Fintype a] [Fintype b] : Fintype.card (Two a b false) = Fintype.card a := rfl
theorem card_two_true (a b : Type) [Fintype a] [Fintype b] : Fintype.card (Two a b true) = Fintype.card b := rfl

def sizeFirst (u v : ℕ) : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1)) :=
  ⟨fun i j => cond i (cond j 1 v) (cond j 0 u), by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · cases i <;> simp [Fintype.sum_bool, card_two_false, card_two_true] <;> omega
    · cases j <;> simp [Fintype.sum_bool, card_two_false, card_two_true] <;> omega⟩

theorem eq_sizeFirst {u v : ℕ} (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1)))
    (h : b.1 false true = 0) : b = sizeFirst u v := by
  have r0 := b.2.1 false
  have r1 := b.2.1 true
  have c1 := b.2.2 true
  simp only [Fintype.sum_bool, card_two_false, card_two_true, Fintype.card_fin] at r0 r1 c1
  refine Subtype.ext (funext fun i => funext fun j => ?_)
  cases i <;> cases j <;> simp [sizeFirst] <;> omega

theorem entry_eq_one {u v : ℕ} (b : SizeMatrix (Two (Fin u) (Fin (v + 1))) (Two (Fin (u + v)) (Fin 1)))
    (h : b.1 false true ≠ 0) : b.1 false true = 1 := by
  have c1 := b.2.2 true
  simp only [Fintype.sum_bool, card_two_false, card_two_true, Fintype.card_fin] at c1
  omega

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.GeometricLemmaFiltration → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ) (e : Fin (u + v) ⊕ Fin 1 ≃ Fin (u + (v + 1))) (ϖ : kˣ), ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)))), Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N, Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) (χ₂ * absPow k (-(1 / 2))))) (detRep (Fin 1) (χ₂ * absPow k ((v : ℂ) / 2))))) ∧ ∀ t, t ≠ t₀ → ∀ w ∈ (S t.succ).toSubmodule, jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂)) (1, GeneralLinearGroup.scalar (Fin 1) ϖ) w - (((χ₁ * absPow k (((u : ℂ) - 1) / 2)) ϖ : ℂˣ) : ℂ) • w ∈ (S t.castSucc).toSubmodule := by
  intro k _ _ _ _ hG χ₁ χ₂ h₁ h₂ u v e ϖ
  have H := hG k Bool Bool (Fin (u + (v + 1))) (Two (Fin u) (Fin (v + 1)))
    (Two (Fin (u + v)) (Fin 1)) (two (stdSum rfl)) (two e)
  refine H.elim fun N hN => hN.elim fun b hb => ?_
  have hb2 := hb _ _ (isSmooth_rhoM h₁ h₂ u (v + 1))
  refine hb2.elim fun S hS => ?_
  have hmono := hS.1
  have h0 := hS.2.1
  have hN := hS.2.2.1
  have hcell := hS.2.2.2
  let S' : Fin (N + 1) → Subrepresentation (jac₂ e (prod₂ (detRep (Fin u) χ₁) (detRep (Fin (v + 1)) χ₂))) :=
    fun t => ⟨(S t).toSubmodule, fun g _ hv => (S t).apply_mem_toSubmodule _ hv⟩
  refine ⟨N, S', fun a c hac => hmono hac, ?_, ?_, b.symm (sizeFirst u v), ?_, ?_⟩
  · exact Subrepresentation.ext (show (S 0).toSubmodule = ⊥ from congrArg Subrepresentation.toSubmodule h0)
  · exact Subrepresentation.ext (show (S (Fin.last N)).toSubmodule = ⊤ from congrArg Subrepresentation.toSubmodule hN)
  · have h00 : (b (b.symm (sizeFirst u v))).1 false true = 0 := by
      rw [Equiv.apply_symm_apply]; rfl
    refine (cellLemma χ₁ χ₂ h₁ h₂ u v _ h00).elim fun f hf => hf.elim fun g hg => hg.elim fun Φ => ?_
    refine (hcell (b.symm (sizeFirst u v)) f g).elim fun Ψ => ?_
    exact ⟨(LocGL.compEquiv Ψ (leviTwo k (Fin (u + v)) (Fin 1)).toMonoidHom).trans Φ⟩
  · intro t ht w hw
    have hbt : (b t).1 false true = 1 := by
      refine entry_eq_one _ fun h => ht ?_
      rw [← eq_sizeFirst (b t) h, Equiv.symm_apply_apply]
    refine (hcell t (b t).nonempty_rows.some (b t).nonempty_cols.some).elim fun Ψ => ?_
    exact step_scalar _ (S t.succ) (S t.castSucc) _ Ψ _ _
      (scalarLemma χ₁ χ₂ u v (b t) hbt (b t).nonempty_rows.some (b t).nonempty_cols.some ϖ) w hw

end GlobalTheory.CellRS
