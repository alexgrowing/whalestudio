import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem iter_lam_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : (P.iter t μ hμ j).J), ∃ (g₀ : P.J) (D : Fin j → GL t k), (g₀ : GL r k).val = (g : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (∀ i, D i ∈ KO k t ∧ (D i).val = Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val i) ∧ (P.iter t μ hμ j).lam g = P.lam g₀ * ∏ i : Fin j, μ (i.val + 1) (Matrix.GeneralLinearGroup.det (D i)) := by
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j
  induction j with
  | zero =>
    intro g
    refine ⟨⟨(reGL (ixZero r t)).symm (g : GL (Ix r t 0) k), g.2⟩, fun i => i.elim0, rfl, fun i => i.elim0, ?_⟩
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | succ j ih =>
    intro g
    let h : (P.iter t μ hμ j).stepJ t := ⟨(reGL (ixSucc r t j)).symm g, g.2⟩
    obtain ⟨D, hD, eD⟩ := h.2.2.2.2.2
    have eu := TypeDatum.corner_val _ h
    have e := TypeDatum.step_lam_eq _ (μ (j + 1)) (hμ _) h _ eu D eD
    obtain ⟨g₀, D', e0, hD', el⟩ := ih (TypeDatum.corner _ h)
    refine ⟨g₀, Fin.snoc (α := fun _ => GL t k) D' D, ?_, ?_, ?_⟩
    · rw [e0, eu]; rfl
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact ⟨hD, by rw [eD]; rfl⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        refine ⟨(hD' i).1, ?_⟩
        rw [(hD' i).2, eu]; rfl
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
      rw [← mul_assoc, ← el]
      exact e

end GlobalTheory.SymBridge
