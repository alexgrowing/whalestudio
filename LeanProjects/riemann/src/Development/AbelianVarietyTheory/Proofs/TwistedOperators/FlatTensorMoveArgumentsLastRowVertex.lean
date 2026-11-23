import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepLeftChangeMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowVertexAdjacentStepsTranslateFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingFilledArgsMoveInnerLastColumnVertexStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DownwardVertexMapLastVertexMulOfFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseLastInnerVertexInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.TopLevelInv.FlatStep
open GlobalTheory.FunObj.FiniteSupport

section Helpers
variable {k : Type} [Field k]

theorem reindex_mul_frameGL {a c b : ℕ} {ι : Type} {a' : ℕ} (h : a + c = b) (f : ι ≃ Fin a') (g : GL (Fin b) k)
    (D : Matrix ι (Fin a ⊕ Fin c) k) :
    D.reindex f (frame h) * g.val = (D * (frameGL h g).val).reindex f (frame h) := by
  ext r s
  simp only [reindex_apply, Matrix.mul_apply, submatrix_apply, frameGL_val]
  exact Fintype.sum_equiv (frame h).symm _ _ fun p => by simp

theorem frameGL_embX_congr {a c c' b : ℕ} (hc : c = c') (h : a + c = b) (h' : a + c' = b) {g : GL (Fin b) k}
    {κ : GL (Fin a) k} (H : frameGL h g = embX c κ) : frameGL h' g = embX c' κ := by
  subst hc; exact H

theorem eq_one_of_mem_symN_zero {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {v : GL (n ⊕ Fin c) k}
    (hv : v ∈ symN k n c) (hc : c = 0) : v = 1 := by
  subst hc
  have key : ∀ p, N k n 0 p = ⊥ := fun p => by
    rw [N, Subgroup.closure_eq_bot_iff]
    intro g hg
    rw [Set.mem_singleton_iff]
    refine Units.ext (Matrix.ext fun r s => ?_)
    rcases r with r | r
    · rcases s with s | s
      · exact hg _ _ le_rfl
      · exact s.elim0
    · exact r.elim0
  rw [symN, key, key, sup_bot_eq, Subgroup.mem_bot] at hv
  exact hv

abbrev StepFam (Γ : Grid k) [MeasurableSpace k] : Type :=
  ∀ i : Fin (Γ.m - 1), (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k) ≃ᵐ
    (StepVar (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i)) → k)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem measurePreserving_stepFam {Γ : Grid k} (ν : Measure k) [ν.IsAddHaarMeasure] (φ : StepFam Γ)
    (hφ : ∀ i, MeasurePreserving (φ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    MeasurePreserving (MeasurableEquiv.piCongrRight φ) (varsVol Γ ν) (varsVol Γ ν) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : ∀ i : Fin (Γ.m - 1), SigmaFinite (stepVol ν (Fin (topRank Γ (i + 1))) (Γ.m - 2 - i) (Fin (topRank Γ i))) :=
    fun i => by unfold stepVol; infer_instance
  rw [varsVol_eq]
  exact measurePreserving_pi _ _ hφ

theorem measurePreserving_update {Γ : Grid k} (ν : Measure k) (Ψ : StepFam Γ)
    (hΨ : ∀ i, MeasurePreserving (Ψ i) (stepVol ν _ _ _) (stepVol ν _ _ _)) (i₀ : Fin (Γ.m - 1))
    (φ : (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k) ≃ᵐ
      (StepVar (Fin (topRank Γ (i₀ + 1))) (Γ.m - 2 - i₀) (Fin (topRank Γ i₀)) → k))
    (hφ : MeasurePreserving φ (stepVol ν _ _ _) (stepVol ν _ _ _)) :
    ∀ i, MeasurePreserving ((Function.update Ψ i₀ φ : StepFam Γ) i) (stepVol ν _ _ _) (stepVol ν _ _ _) := by
  intro i
  rcases eq_or_ne i i₀ with rfl | h
  · rw [Function.update_self]; exact hφ
  · rw [Function.update_of_ne h]; exact hΨ i

theorem flatTensor_comp_of_equiv {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (F : Γ.Args → ℂ)
    (A : Γ.Args → Γ.Args) (x x' : ColArgs Γ) (y : RowArgs Γ) (Φ : Vars Γ ≃ᵐ Vars Γ)
    (hΦ : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν))
    (hfill : ∀ e, A (fill hs x y e) = fill hs x' y (Φ e)) (hph : ∀ e, phase x e = phase x' (Φ e)) :
    flatTensor hs ψ ν (fun z => F (A z)) x y = flatTensor hs ψ ν F x' y := by
  rw [flatTensor, flatTensor, ← hΦ.integral_comp' (flatIntegrand hs ψ F x' y)]
  congr 1
  funext e
  simp only [flatIntegrand, hfill, hph]

theorem downMap_congr {Γ : Grid k} (hs : 1 ≤ Γ.s) {x x' : ColArgs Γ} {e e' : Vars Γ} {l : ℕ} (hx : x' l = x l)
    (he : ∀ h : l < Γ.m - 1, e' ⟨l, h⟩ = e ⟨l, h⟩) : downMap hs x' e' l = downMap hs x e l := by
  unfold downMap
  split_ifs with h1
  · rw [hx, he h1]
  · rw [hx]
  · rfl

end Helpers

theorem flatTensor_moveArgs_mulSingle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (F : Γ.Args → ℂ)
    (j : ℕ) (hj : j + 1 < Γ.m) (g : GL (Fin (Γ.rank (Γ.m, j + 1))) k) (κ : GL (Fin (topRank Γ (j + 1))) k),
    valuation k (gdet κ : k) = 1 → ∀ v ∈ symN k (Fin (topRank Γ (j + 1))) (Γ.m - 1 - (j + 1)), toFrame hs hj g = v * embX _ κ →
    ∀ (x : ColArgs Γ) (y : RowArgs Γ),
      flatTensor hs ψ ν (fun z => F (Γ.moveArgs .one (Pi.mulSingle (Γ.m, j + 1) g) z)) x y = flatTensor hs ψ ν F (colMove j κ x) y := by
  intro k _ _ _ _ _ _ Γ hs ψ ν _ F j hj g κ hdet v hv hg x y
  have hcol : ∀ i, i ≠ j → i ≠ j + 1 → colMove j κ x i = x i := fun i h1 h2 => by
    simp only [colMove, Function.update_of_ne h1, Function.update_of_ne h2]
  have hcj : colMove j κ x j = (κ⁻¹).val * x j := by
    simp only [colMove, Function.update_of_ne (show j ≠ j + 1 by omega), Function.update_self]
  have hcj1 : colMove j κ x (j + 1) = x (j + 1) * κ.val := by
    simp only [colMove, Function.update_self]
  rcases Nat.lt_or_ge (j + 2) Γ.m with hA | hB
  · obtain ⟨φ₀, hφ₀, φ₁, hφ₁, H⟩ := GlobalTheory.T.lastRowVertex_adjacentSteps_translate_frames (a₀ := topRank Γ j) (a₂ := topRank Γ (j + 1 + 1))
      (c := Γ.m - 2 - (j + 1)) (c₀ := Γ.m - 2 - j) ν (by omega) (by omega)
      (by have := topRank_add hs (j + 1); omega) (by have := topRank_add hs (j + 1); omega) _ g κ hdet v hv hg
      (x j) (x (j + 1))
    have h01 : (⟨j, by omega⟩ : Fin (Γ.m - 1)) ≠ ⟨j + 1, by omega⟩ := fun h => by simp at h
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Ψ2 : StepFam Γ := Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ2
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_of_ne h01]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦ1 : ∀ e, Φ e ⟨j + 1, by omega⟩ = φ₁ (e ⟨j + 1, by omega⟩) := fun e => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ ⟨j + 1, by omega⟩ (e ⟨j + 1, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → i.val ≠ j + 1 → Φ e i = e i := fun e i h1 h2 => by
      show Function.update Ψ1 ⟨j + 1, by omega⟩ φ₁ i (e i) = _
      rw [Function.update_of_ne (fun h => h2 (by rw [h]))]
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ2 (measurePreserving_update ν Ψ1
        (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀) ⟨j + 1, by omega⟩ φ₁ hφ₁)
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1 h2
      · rw [downMap, dif_pos (show j < Γ.m - 1 by omega), downMap, dif_pos (show j < Γ.m - 1 by omega), hcj, hΦ0]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).1 _).symm
      · rw [downMap, dif_pos (show j + 1 < Γ.m - 1 by omega), downMap, dif_pos (show j + 1 < Γ.m - 1 by omega),
          hcj1, hΦ1]
        exact ((H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.1 _).symm
    · have hrow : ∀ (x : ColArgs Γ) (e : Vars Γ) r, rowVar x e (j + 1) r = ∑ l : Fin (Γ.m - 2 - (j + 1)),
          if l.val = (Γ.m - 2 - (j + 1)) / 2 then stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩) (.inr l) (.inl r) else 0 :=
        fun x e r => by rw [rowVar, dif_pos (by omega)]
      refine GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant j hA x (colMove j κ x) e (Φ e) hcol (fun i h1 h2 => hΦo e i h1 h2) ?_ ?_ ?_
      · simp only [hrow, colVar]
        rw [hcj, hcj1, hΦ0, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.1
      · intro ho s
        rw [rowVar, rowVar, dif_pos (by omega), dif_pos (by omega)]
        refine Finset.sum_congr rfl fun l _ => ?_
        split_ifs with hl
        · rw [hcj, hΦ0]
          exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.1 ho l s hl
        · rfl
      · intro ho r
        simp only [colVar]
        rw [hcj1, hΦ1]
        exact (H (e ⟨j, by omega⟩) (e ⟨j + 1, by omega⟩)).2.2.2.2 ho r _ rfl
  · have hB' : j + 2 = Γ.m := by omega
    obtain rfl : v = 1 := eq_one_of_mem_symN_zero hv (by omega)
    have hg' : toFrame hs hj g = embX _ κ := by rw [hg, one_mul]
    obtain ⟨φ₀, hφ₀, H⟩ := GlobalTheory.T.fourierJacobiStep_leftChange_measurePreserving (n := Fin (topRank Γ (j + 1))) (n' := Fin (topRank Γ j)) (c := Γ.m - 2 - j)
      ν 1 (one_mem _) κ hdet (x j)
    let Ψ0 : StepFam Γ := fun i => MeasurableEquiv.refl _
    let Ψ1 : StepFam Γ := Function.update Ψ0 ⟨j, by omega⟩ φ₀
    let Φ : Vars Γ ≃ᵐ Vars Γ := MeasurableEquiv.piCongrRight Ψ1
    have hΦ0 : ∀ e, Φ e ⟨j, by omega⟩ = φ₀ (e ⟨j, by omega⟩) := fun e => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ ⟨j, by omega⟩ (e ⟨j, by omega⟩) = _
      rw [Function.update_self]
    have hΦo : ∀ e (i : Fin (Γ.m - 1)), i.val ≠ j → Φ e i = e i := fun e i h1 => by
      show Function.update Ψ0 ⟨j, by omega⟩ φ₀ i (e i) = _
      rw [Function.update_of_ne (fun h => h1 (by rw [h]))]
      rfl
    have hMP : MeasurePreserving Φ (varsVol Γ ν) (varsVol Γ ν) :=
      measurePreserving_stepFam ν Ψ1 (measurePreserving_update ν Ψ0 (fun i => MeasurePreserving.id _) ⟨j, by omega⟩ φ₀ hφ₀)
    have hf : frameGL (show topRank Γ (j + 1) + (Γ.m - 2 - j) = Γ.rank (Γ.m, j + 1) by
        have := topRank_add hs (j + 1); omega) g = embX (Γ.m - 2 - j) κ :=
      frameGL_embX_congr (by omega) _ _ hg'
    refine flatTensor_comp_of_equiv hs ψ ν F _ x (colMove j κ x) y Φ hMP (fun e => ?_) (fun e => ?_)
    · refine GlobalTheory.T.unfoldingFilledArgs_moveInnerLastColumnVertex hs j hj g x (colMove j κ x) y e (Φ e) (fun l h1 h2 => ?_) ?_ ?_
      · exact downMap_congr hs (hcol l h1 h2) fun h => hΦo e ⟨l, h⟩ h1
      · rw [downMap, dif_pos (show j < Γ.m - 1 by omega), downMap, dif_pos (show j < Γ.m - 1 by omega), hcj, hΦ0,
          ← H, one_mul, mul_reindex, map_inv, hf]
      · exact GlobalTheory.T.downwardVertexMap_lastVertex_mul_of_frame hs j hj hB' g κ hg' x (colMove j κ x) e (Φ e) hcj1
    · refine GlobalTheory.T.fourierJacobiPhase_lastInnerVertex_invariant j hB' κ x (colMove j κ x) e (Φ e) hcol hcj1 (fun i h1 => hΦo e i h1) ?_
      rw [hcj, hΦ0, ← H, one_mul]

end GlobalTheory.TopLevelInv.FlatStep
