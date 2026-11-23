import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardCharStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiActRight

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid GlobalTheory.BiTransfer

variable {D : D7}

theorem conjSource_conjAdjoint_apply {S A' : HSp D} (omb : Om S A') (g : GA D S) (h : GA D A') (f : WO S A' → ℂ)
    (y : WO A' S) :
    conjSource (conjAdjoint omb) (negGA A' h, g) (fun y' => f (dagger A' S y')) y = omb (g, h) f (dagger A' S y) := by
  have e1 : conjSource (conjAdjoint omb) (negGA A' h, g) =
      cjEnd (Equiv.refl (WO A' S)) (cjEnd (daggerEquiv S A') (omb (g, h))) := by
    simp only [conjSource, conjAdjoint, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.coe_mk, OneHom.coe_mk,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.id_apply, Prod.map]
    rfl
  have e2 : (fun y' => f (dagger A' S y')) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (Equiv.refl (WO A' S)) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (daggerEquiv S A') f) := by
    funext y'; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]
  rw [e1, e2, cjEnd_cj, cjEnd_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, daggerEquiv]

theorem resS_symm_swap {W A B : HSp D} (d : OrthDec W A B) (T : HSp D) (u : WO A T) (y : WO B T) :
    (d.symm.resS T).symm (y, u) = (d.resS T).symm (u, y) :=
  add_comm (y ⬝ d.pB) (u ⬝ d.pA)

theorem isBiTheta_act_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χS' χA' : (AE D)ˣ →* Circle) (omb : Om S A'), IsWeilDatumO ψ S A' χS' χA' omb → ∀ C, IsBiTheta ψ A S A' C → ∀ q, IsBiTheta ψ A S A' fun u v => omb q (C u) v := by
  intro D ψ A S A' χS' χA' omb hω C hC q
  obtain ⟨g, h⟩ := q
  have hw1 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std S A').conj_adjoint χS' χA' omb hω).1
  have hw2 := ((GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hω.std A' S).conj_source χA' χS' (conjAdjoint omb) hw1).1
  let d := sumDec A (negSp A')
  have hG := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ (negSp A') A S d.symm _ _ (conjSource (conjAdjoint omb)) hw2 _ (isThetaFunO_join d hC)
    Unit 0 (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) (negGA A' h, g)).1
  refine isBiTheta_of_join d ?_
  convert hG using 1
  funext x
  simp only [resS_symm_swap, join_symm]
  exact (conjSource_conjAdjoint_apply omb g h (C (d.resS S x).1) (d.resS S x).2).symm

end GlobalTheory.BiActRight

end
