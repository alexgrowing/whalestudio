import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacBridge

theorem rho_acts_locCo : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  intro F _ _ W _ _ B κ _ co ψ v γ hγ φ r hr
  funext x
  set w := co.e γ with hw
  have hcomp : ∀ u : AF F, GlobalTheory.AdelicU.evFin F v u = 0 → u • w = 0 := fun u hu => by
    rw [hw, ← LinearEquiv.map_smul, hγ u hu, map_zero]
  have ha1 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.1 k) := fun k u hu => by
    have := congrArg (fun z => z.1 k) (hcomp u hu)
    simpa using this
  have ha2 : ∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (w.2 k) := fun k u hu => by
    have := congrArg (fun z => z.2 k) (hcomp u hu)
    simpa using this
  have hshift : r (x + w.1) = r x := hr.1 x w.1 (GlobalTheory.VacAny.at_pi ha1)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, ← hw, hshift]
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) :=
    GlobalTheory.VacAny.at_add (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (ha2 k))
      (GlobalTheory.VacAny.at_mul_left _ (GlobalTheory.VacAny.at_sum _ fun k _ => GlobalTheory.VacAny.at_mul_left _ (ha2 k)))
  rw [GlobalTheory.StdVacuum.psi_eq_psiLoc ψ v _ hat, ← GlobalTheory.LatVac.psiAt_apply]
  have e1 : GlobalTheory.AdelicU.evFin F v (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        ⅟(2 : Fv F v) * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2) := by
    simp only [dotProduct, map_add, map_sum, map_mul, GlobalTheory.VacAny.evFin_invOf_two, hw]
    rfl
  have e2 : (fun i => GlobalTheory.AdelicU.evFin F v ((x + w.1) i)) =
      (fun i => GlobalTheory.AdelicU.evFin F v (x i)) + (GlobalTheory.LatVac.locCo co v γ).1 := by
    funext i
    simp only [Pi.add_apply, map_add, hw]
    rfl
  rw [e1, e2, mul_assoc]

end GlobalTheory.VacBridge
