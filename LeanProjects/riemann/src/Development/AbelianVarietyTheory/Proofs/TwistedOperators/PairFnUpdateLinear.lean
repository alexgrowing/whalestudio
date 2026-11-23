import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearMapChainCompositeUpdateSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkV_add (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (f + f') a b = kkV S p f a b + kkV S p f' a b :=
  GlobalTheory.TopZeroInv.kkVec_add S p hf hf' a b

theorem kkV_smul (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (a : FinPt G p.small) (b : FinPt G p.big) :
    kkV S p (c • f) a b = c • kkV S p f a b :=
  GlobalTheory.TopZeroInv.kkVec_smul S p c f a b

theorem colV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ j, v (.inl j) = v' (.inl j))
    (x : ∀ j, FinPt G (.top j)) : colV S v x = colV S v' x := by
  have e : (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) =
      (fun j => if h : j < D.R.m then kkV S (.top t j) (v' (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    funext j; split_ifs with hj
    · rw [h]
    · rfl
  simp only [colV, e]

theorem rowV_congr (S : GridChoice W U) {t : T} {v v' : ∀ a, FactorFn G t a} (h : ∀ i, v (.inr i) = v' (.inr i))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : rowV S v y = rowV S v' y := by
  have e : (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v' (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    funext i; split_ifs with hi
    · rw [h]
    · rfl
  simp only [rowV, e]

theorem colK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) (j₀ : Fin D.R.m)
    (F : FactorFn G t (.inl j₀)) :
    (fun j => if h : j < D.R.m then kkV S (.top t j) (Function.update v (.inl j₀) F (.inl ⟨j, h⟩)) (x j) (x (j + 1))
      else 0) =
    Function.update (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) j₀.1
      (kkV S (.top t j₀.1) F (x j₀.1) (x (j₀.1 + 1))) := by
  funext j
  by_cases hj : j = j₀.1
  · subst hj
    rw [Function.update_self, dif_pos j₀.2]
    show kkV S (.top t j₀.1) (Function.update v (.inl j₀) F (.inl j₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hj]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hj (congrArg Fin.val (Sum.inl_injective e))
    · rfl

theorem rowK_update (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) (i₀ : Fin D.R.m)
    (F : FactorFn G t (.inr i₀)) :
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (Function.update v (.inr i₀) F (.inr ⟨i, h⟩)) (y i) (y (i + 1))
      else 0) =
    Function.update (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) i₀.1
      (kkV S (.chi i₀.1 D.R.m) F (y i₀.1) (y (i₀.1 + 1))) := by
  funext i
  by_cases hi : i = i₀.1
  · subst hi
    rw [Function.update_self, dif_pos i₀.2]
    show kkV S (.chi i₀.1 D.R.m) (Function.update v (.inr i₀) F (.inr i₀)) _ _ = _
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e; exact hi (congrArg Fin.val (Sum.inr_injective e))
    · rfl

theorem pairFn_apply (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) (p : VV ℂ (wt G (.top 0))) (q : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    pairFn S x y v p q =
      brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (colV S v x p) (rowV S v y q) := rfl

theorem pairFn_update_linear : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (v : ∀ a, FactorFn G t a), (∀ a, v a ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a))) → ∀ (a : Fin D.R.m ⊕ Fin D.R.m) (f g : FactorFn G t a), f ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → g ∈ thetaSub W.ψ (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → pairFn S x y (Function.update v a (f + g)) = pairFn S x y (Function.update v a f) + pairFn S x y (Function.update v a g) ∧ ∀ c : ℂ, pairFn S x y (Function.update v a (c • f)) = c • pairFn S x y (Function.update v a f) := by
  intro D T L sc G W U S t x y v _ a f g hf hg
  rcases a with j₀ | i₀
  · have hr : ∀ F, rowV S (Function.update v (.inl j₀) F) y = rowV S v y := fun F =>
      rowV_congr S (fun i => Function.update_of_ne Sum.inr_ne_inl _ _) y
    have hadd : colV S (Function.update v (.inl j₀) (f + g)) x =
        colV S (Function.update v (.inl j₀) f) x + colV S (Function.update v (.inl j₀) g) x := by
      have h : kkV S (.top t j₀.1) (f + g) (x j₀.1) (x (j₀.1 + 1)) =
          kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) + kkV S (.top t j₀.1) g (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_add S (.top t j₀.1) hf hg _ _
      rw [colV, colV, colV, colK_update, colK_update, colK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ j₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, colV S (Function.update v (.inl j₀) (c • f)) x = c • colV S (Function.update v (.inl j₀) f) x := by
      intro c
      have h : kkV S (.top t j₀.1) (c • f) (x j₀.1) (x (j₀.1 + 1)) = c • kkV S (.top t j₀.1) f (x j₀.1) (x (j₀.1 + 1)) :=
        kkV_smul S (.top t j₀.1) c f _ _
      rw [colV, colV, colK_update, colK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ j₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hr, hr, hr, hadd,
        LinearMap.add_apply]
      exact LinearMap.map_add₂ _ _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hr, hr, hsmul, LinearMap.smul_apply]
      exact LinearMap.map_smul₂ _ _ _ _
  · have hc : ∀ F, colV S (Function.update v (.inr i₀) F) x = colV S v x := fun F =>
      colV_congr S (fun j => Function.update_of_ne Sum.inl_ne_inr _ _) x
    have hadd : rowV S (Function.update v (.inr i₀) (f + g)) y =
        rowV S (Function.update v (.inr i₀) f) y + rowV S (Function.update v (.inr i₀) g) y := by
      have h : kkV S (.chi i₀.1 D.R.m) (f + g) (y i₀.1) (y (i₀.1 + 1)) =
          kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) + kkV S (.chi i₀.1 D.R.m) g (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_add S (.chi i₀.1 D.R.m) hf hg _ _
      rw [rowV, rowV, rowV, rowK_update, rowK_update, rowK_update, h,
        GlobalTheory.chainTo_update_add _ _ _ _ _ i₀.2, LinearMap.add_comp]
    have hsmul : ∀ c : ℂ, rowV S (Function.update v (.inr i₀) (c • f)) y = c • rowV S (Function.update v (.inr i₀) f) y := by
      intro c
      have h : kkV S (.chi i₀.1 D.R.m) (c • f) (y i₀.1) (y (i₀.1 + 1)) = c • kkV S (.chi i₀.1 D.R.m) f (y i₀.1) (y (i₀.1 + 1)) :=
        kkV_smul S (.chi i₀.1 D.R.m) c f _ _
      rw [rowV, rowV, rowK_update, rowK_update, h, GlobalTheory.ChainSmul.chainTo_update_smul _ _ _ _ _ i₀.2,
        LinearMap.smul_comp]
    refine ⟨?_, fun c => ?_⟩
    · ext p q
      rw [LinearMap.add_apply, LinearMap.add_apply, pairFn_apply, pairFn_apply, pairFn_apply, hc, hc, hc, hadd,
        LinearMap.add_apply]
      exact map_add _ _ _
    · ext p q
      rw [LinearMap.smul_apply, LinearMap.smul_apply, pairFn_apply, pairFn_apply, hc, hc, hsmul, LinearMap.smul_apply]
      exact map_smul _ _ _

end GlobalTheory.RowVertexInv
