import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PublishedInputsThirdLayer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypicStatement
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixSph
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.FixOne
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.LevSplit
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedNeBotOfMemSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M.B

theorem good_of_fix {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W))
    (hS : NG.IsIrrRep a.ρ S) (s : SplitPlace L) {p : Prop}
    (hp : p → ∃ (g : ℕ) (_ : Fact g.Prime) (i : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i) (f : GAf L n → a.W) (hf : f ∈ S)
    (hf0 : f ≠ 0) (hff : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (p → IsPrincipalCongruenceAt s κ) → NG.rt L n κ f = f) (σ) (hσ : IsLocS S s σ) :
    UpperTheory.Zero.LLC.Good (GlobalTheory.LocLanglands.cls σ) := by
  by_cases h : p
  · have h1 := fixOne L n a S hS s f hf hf0 (fun κ x y z => hff κ x y fun _ => z) σ hσ
    exact GlobalTheory.AVGood.good_of_fixed_KOne UpperTheory.Zero.LLC.Pr.zel (hp h) _
      (GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm h1)
  · exact GlobalTheory.AVGood.good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz _
      (GlobalTheory.LocLanglands.fixed_ne_bot_of_equiv (GlobalTheory.SmGL.IrrRep.nonempty_equiv_rep σ).some.symm
        (fixSph L n a S hS s f hf hf0 (fun κ x y => hff κ x y fun z => absurd z h) σ hσ))

end UpperTheory.One.M.B
