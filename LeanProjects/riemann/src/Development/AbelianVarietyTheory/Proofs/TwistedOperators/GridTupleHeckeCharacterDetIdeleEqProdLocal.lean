import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAtStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartComponStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem chrEq_mu_succ_succ : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ChrEq (L.mu t (j + 1 + 1)) (muBase L (j + 1 + 1) * L.xiH t) ∧ ∀ P, (muBase L (j + 1 + 1) * L.xiH t).TameAt P := by
  intro D T L μ₀ hL t j hj
  have hm : ChrEq (L.mu0 (j + 1 + 1)) (muBase L (j + 1 + 1)) := by
    have := hL.mu0 ⟨j + 1, hj⟩
    simpa [muBase, hj] using this
  refine ⟨GlobalTheory.TowerCharRead.chrEq_mul hm (hL.xi t), fun P => ?_⟩
  have h1 : (muBase L (j + 1 + 1)).TameAt P := by
    rw [muBase, dif_pos hj]; exact (L.C.isMu0 ⟨j + 1, hj⟩).tame P
  exact Formalism.L2.Host.HChar.LevelLe.mul h1 (hL.xi_tame t P)

theorem mu_detAt_eq_prod_loc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he
  obtain ⟨hχ, htame⟩ := chrEq_mu_succ_succ hL t j hj
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components he (G.V (.top (j + 1)))
    ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))
  rw [GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt hχ (locPl G t) (fun P _ => htame P) (fun P => gdet (kapAt S t j hj k P)) _ hinf
    (fun P hP => (hin P hP).trans (GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent S t j hj k _ P)) hout]
  rw [← Finset.prod_coe_sort]
  rfl

end GlobalTheory.TopLevelInv
