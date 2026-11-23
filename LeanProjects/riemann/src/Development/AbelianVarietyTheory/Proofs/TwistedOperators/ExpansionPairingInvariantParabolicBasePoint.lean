import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCompMulFin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairVecSumEqOfProdEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecIsThetaFunO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem pairVec_move (S : GridChoice W U) {t : T} (fs : Vecs G t) (hf : IsThetaFunO W.ψ _ _ (fs first))
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)) :
    pairVec S (Function.update x 0 (x 0 * k)) y fs =
      pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) := by
  have hj : ∀ j, (if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) := by
    intro j
    by_cases h : j < D.R.m
    · rw [dif_pos h, dif_pos h]
      rcases j with _ | j
      · have e1 : Function.update x 0 (x 0 * k) 0 = x 0 * k := Function.update_self _ _ _
        have e2 : Function.update x 0 (x 0 * k) (0 + 1) = x (0 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨0, h⟩) =
            W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (fs first) :=
          Function.update_self _ _ _
        rw [e1, e2, e3]
        unfold kkVec
        have e4 : x 0 * k * S.N.u (Pair.small (.top t 0)) =
            (x 0 * S.N.u (.top 0)) * ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) := by group
        rw [e4, GlobalTheory.KerTrans.fockComp_mul_fin W _ (p := .top t 0) (show (Pair.top t 0 : Pair T).InRange D.R.m from
          show 1 ≤ D.R.m by have := D.R.two_le_m; omega) (fs (.inl ⟨0, h⟩)) hf]
        rfl
      · have e1 : Function.update x 0 (x 0 * k) (j + 1) = x (j + 1) := Function.update_of_ne (by omega) _ _
        have e2 : Function.update x 0 (x 0 * k) (j + 1 + 1) = x (j + 1 + 1) := Function.update_of_ne (by omega) _ _
        have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j + 1, h⟩) = fs (.inl ⟨j + 1, h⟩) :=
          Function.update_of_ne (by simp [first]) _ _
        rw [e1, e2, e3]
    · rw [dif_neg h, dif_neg h]
  have hcol : colV S fs (Function.update x 0 (x 0 * k)) =
      colV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) x := by
    have hfam : (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (Function.update x 0 (x 0 * k) j)
          (Function.update x 0 (x 0 * k) (j + 1)) else 0) =
        (fun j => if h : j < D.R.m then kkVec S (.top t j)
          (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) :=
      funext hj
    unfold colV
    rw [hfam]
  have hri : ∀ i, (if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := by
    intro i
    by_cases h : i < D.R.m
    · rw [dif_pos h, dif_pos h]
      have e3 : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩) = fs (.inr ⟨i, h⟩) :=
        Function.update_of_ne (by simp [first]) _ _
      rw [e3]
    · rw [dif_neg h, dif_neg h]
  have hrow : rowV S fs y = rowV S (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs) y := by
    have hfam : (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) =
      (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m)
        (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) := funext hri
    unfold rowV
    rw [hfam]
  unfold pairVec
  rw [hcol, hrow]

theorem pairPts_update_top_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    (∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hq hc ht hβ hτ hv Ψ F hΨ x y k hk
  have hk' : finG (G.V (.top 0)) k ∈ G.Kplus := hk
  rw [hΨ _ _ hk', pairPts_eq, pairPts_eq]
  have hth : ∀ d ∈ τ.support, ∀ l, IsThetaFunO W.ψ _ _ (vecsOf S d l) := fun d hd l => by
    rcases l with j | i
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .top t j) (show DefPair D.R.m (Pair.top t (j : ℕ)) from j.2) _ ((hv d hd).1 j)
    · exact GlobalTheory.TopZeroInv.vec_isThetaFunO S (p := .chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) _ ((hv d hd).2 i)
  have hp0 : (Pair.top t 0 : Pair T).InRange D.R.m := show 1 ≤ D.R.m by have := D.R.two_le_m; omega
  have hmv : ∀ d ∈ τ.support, ∀ l,
      IsThetaFunO W.ψ _ _ (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l) := by
    intro d hd l
    by_cases hl : l = first
    · subst hl
      have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) first =
          W.om (.top t 0) (G.toPair (.top t 0) ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)).1 1) (vecsOf S d first) :=
        Function.update_self _ _ _
      rw [e]
      exact (W.om_is _ hp0).om_pres _ _ (hth d hd first)
    · have e : moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l = vecsOf S d l :=
        Function.update_of_ne hl _ _
      rw [e]
      exact hth d hd l
  calc (τ.sum fun d a => a * pairVec S (Function.update x 0 (x 0 * k)) y (vecsOf S d) (Ψ (x 0)) (F (y 0)))
      = τ.sum fun d a => a * pairVec S x y (moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d))
          (Ψ (x 0)) (F (y 0)) :=
        Finset.sum_congr rfl fun d hd => by dsimp only; rw [pairVec_move S _ (hth d hd first)]
    _ = τ.sum fun d a => a * pairVec S x y (vecsOf S d) (Ψ (x 0)) (F (y 0)) :=
        GlobalTheory.TopZeroInv.pairVec_sum_eq_of_prod_eq S τ _ _ x y _ _ hmv hth (GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus S ht hL hq hc ht hβ hτ hv k hk')

end GlobalTheory.TopZeroInv
