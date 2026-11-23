import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChartA

open GlobalTheory.FlipMatch.RowChart GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk)

theorem tr_full {k : Type} [Field k] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) {b β g : GL (Fin n) k}
    {Gm : Matrix (Fin n) (Fin n) k} (hg : g.val = -(β.valᵀ * Gmᵀ * b.val))
    {c cc : GL (Fin d) k} {βV : GL (Fin p) k} {β₁ : GL (Fin q) k} (hC : c.val * cc.val = blk e βV.val (-β₁.val))
    (U : Matrix (Fin n) (Fin d) k) :
    g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (blk e (βV⁻¹).val (-(β₁⁻¹).val) * (Uᵀ * -Gm) * β.val)ᵀ := by
  have h : g.val * ((b⁻¹).val * U * (c⁻¹).valᵀ) * (invT cc).val =
      (-(β.valᵀ * Gmᵀ) * U) * blk e (βV⁻¹).valᵀ (-(β₁⁻¹).valᵀ) := by
    rw [← inv_of_blk e hC, invT_val, hg]
    simp only [Matrix.neg_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b.val, Units.mul_inv, Matrix.one_mul]
  rw [h]
  simp only [transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose]

theorem map_frame {A R k : Type} [CommRing A] [CommRing R] [Field k] (f : A →+* R) (c : R →+* k) {n p q d : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin d) (β : GL (Fin n) R) (βV : GL (Fin p) R) (β₁ : GL (Fin q) R)
    (J : Matrix (Fin n) (Fin n) A) (u : Matrix (Fin n) (Fin d) A) :
    (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val *
        (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id * J).map f * β.val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val) *
        ((u.map (c.comp f))ᵀ * J.map (c.comp f)) * (GeneralLinearGroup.map c β).val).submatrix
        (e.symm.trans finSumFinEquiv).symm id := by
  have h1 : (((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val).map c =
      (blk e ((GeneralLinearGroup.map c βV)⁻¹).val (-((GeneralLinearGroup.map c β₁)⁻¹).val)).submatrix
        (e.symm.trans finSumFinEquiv).symm (e.symm.trans finSumFinEquiv).symm := by
    have h0 : ((GlobalTheory.Doubling.blkGL finSumFinEquiv (βV, -β₁))⁻¹).val =
        GlobalTheory.Doubling.blkMat finSumFinEquiv (βV⁻¹).val (-(β₁⁻¹).val) := rfl
    rw [h0, GlobalTheory.Doubling.blkMat_map _ _ (map_zero c), Matrix.map_neg _ (map_neg c)]
    ext a b
    simp only [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, submatrix_apply, reindex_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_apply_apply]
    rfl
  rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.map_mul, Matrix.map_mul]
  have h2 : ((uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id).map f).map c * (J.map f).map c =
      ((u.map (c.comp f))ᵀ * J.map (c.comp f)).submatrix (e.symm.trans finSumFinEquiv).symm id := rfl
  rw [h2, submatrix_mul_equiv]
  rfl

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
  (i j : Fin D.R.m) (e : Num G i j)

theorem linA_ptA (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linA B t i j w (ptA e u) = reindex (finCongr (rankW G t i j w)) (colsEq t e w)
      (blk e ((loc w (B.β i (j + 1)))⁻¹).val (-((loc w (B.β (i + 1) j))⁻¹).val) *
        HMul.hMul (u.map (cw w))ᵀ (-(spW G i j).gram.map (algebraMap D.host.E (Kw w))) *
        (loc w (B.β (i + 1) (j + 1))).val)ᵀ := by
  have eJ : (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram).map (cw w) =
      -(spW G i j).gram.map (algebraMap D.host.E (Kw w)) :=
    Matrix.ext fun a b => (Good.cpt_incA _ _).trans (map_neg (algebraMap D.host.E (Kw w)) _)
  have k2 := map_frame (toEAf D) (cpt (D := D) w) (n := (spW G i j).rank) e (B.β (i + 1) (j + 1)) (B.β i (j + 1))
    (B.β (i + 1) j) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) u
  rw [← eJ]
  refine Matrix.ext fun r s => ?_
  refine (congrFun (congrFun k2 ((colX G t i j w).symm s)) ((finCongr (rankW G t i j w)).symm r)).trans ?_
  have hs : (e.symm.trans finSumFinEquiv).symm ((colX G t i j w).symm s) = (colsEq t e w).symm s :=
    congrArg e (finSumFinEquiv.symm_apply_apply _)
  rw [submatrix_apply, hs]
  rfl

theorem chart_eq_linA (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) {v : Pl D.host.F}
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E) (ψ : Fv D.host.F v ≃+* Kw w) (hjj : IsPlaceIso τ w ψ)
    (cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w))
    (hcc : (Γ.W.bas v).val.map ψ * cc.val = basCols B e w) (g : GL (Fin (spW G i j).rank) (Kw w))
    (hg : g.val = -((loc w (B.β (i + 1) (j + 1))).valᵀ *
      ((spW G i j).gram.map (algebraMap D.host.E (Kw w)))ᵀ * (Γ.V.bas v).val.map ψ))
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    chart ψ (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX τ (Γ.V.bas v) (Γ.W.bas v) u) =
      linA B t i j w (ptA e u) := by
  have eU : (u.map (piW τ)).map ψ = u.map (cw w) := Matrix.ext fun a b => hjj _
  have k1 := tr_full e (b := GeneralLinearGroup.map ψ.toRingHom (Γ.V.bas v))
    (c := GeneralLinearGroup.map ψ.toRingHom (Γ.W.bas v)) (β := loc w (B.β (i + 1) (j + 1)))
    (βV := loc w (B.β i (j + 1))) (β₁ := loc w (B.β (i + 1) j)) hg hcc (u.map (cw w))
  rw [linA_ptA, chart, chart_coX, eU]
  exact congrArg _ k1

end Grid

theorem exists_mixChart_lin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsTied t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g ∈ KO (Kw w) (Fin (spW G i j).rank),
      IsMixChart v.1 (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w)
        (fun u => chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW G t i j w)) (colsEq t e w) (invT g) cc
          (coY D.sp.cm.sig Γ.V Γ.W (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _)ᶜ ∧
      ∀ u, chart jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) (coX (Bs.τ v) (Γ.V.bas v) (Γ.W.bas v) u) =
        linA B t i j w (ptA e u) := by
  classical
  intro D T L sc G μ₀ hL W B t i j M _ e Bs Γ X om om' h hT hTi v w hw jj hjj _ cc hcc
  subst hw
  obtain rfl := eq_complEquiv _ hjj
  have hV := hT.geo.hV
  have hJT : IsHermND D.sp.cm.sig Γ.V.Jᵀ := ⟨fun i j => by simpa using hV.herm j i, by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm _ Bs hV⟩
  have hsd := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose _ _ _ Bs _ Γ.V _ _ hT.base hV v
  have hb := hV.bas v
  rw [hTi.1] at hsd hb
  obtain ⟨g, hgK, hg⟩ := exists_rows (Bs.τ v) hJT hsd hb
    (isFrameAt_loc (B.isFrame_β hL (i := (i : ℕ) + 1) (j := (j : ℕ) + 1) i.2 j.2) (splitPrime (Bs.τ v)))
  have hJW : Γ.V.J = (spW G i j).gram := h.JW.trans (one_smul _ _)
  rw [hJW] at hg
  refine ⟨g, hgK, isMixChart_of B t i j e Γ (Bs.τ v) _ hjj (complMap_apply_emb _ _) hJW h.JWW cc hcc g hg, fun u => ?_⟩
  exact chart_eq_linA B t i j e Γ (Bs.τ v) _ _ hjj cc hcc g hg u

end GlobalTheory.TopFlip.ChartA

end
