import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialisedUniversalSeriesEqTwistedThetaSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

open MvPolynomial

private theorem jetLin_add_tab {K : Type} [Field K] {ι : Type} {a b : ℕ} (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add]

theorem kkVec_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  intro D T L sc G W U S p f f' hf hf' x y
  have hJ : ∀ x' y', GlobalTheory.FunObj.jetTab W S.N.frC p (f + f') x' y' =
      GlobalTheory.FunObj.jetTab W S.N.frC p f x' y' + GlobalTheory.FunObj.jetTab W S.N.frC p f' x' y' := by
    intro x' y'
    funext k
    simp only [GlobalTheory.FunObj.jetTab, GlobalTheory.FunObj.kerFin, GlobalTheory.FunObj.fockIn, Pi.add_apply]
    rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf']
    simp only [GlobalTheory.ChiGrid.GridData.Weil.ker, thetaKO, map_add, Pi.add_apply]
  unfold kkVec GlobalTheory.FunObj.fockComp
  rw [hJ, ← smul_add]
  congr 1
  ext1 F
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add_tab, LinearMap.comp_apply, LinearMap.add_apply, map_add]

end GlobalTheory.TopZeroInv
