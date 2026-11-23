import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zetaIdentity_persists_row_column_changes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a a₁ : ℕ) (ha : a = a₁) (A' : Type) [Fintype A'] [DecidableEq A'] (A₁ : Type) [Fintype A₁] [DecidableEq A₁] (C : Type) [Fintype C] [DecidableEq C] (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eB : A' ≃ A₁) (eC : C ≃ C₁)
    (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a₁ ⊕ A₁ ≃ C₁) (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (μ₁ : Measure (GL A₁ k)) [μ₁.IsHaarMeasure]
    (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) →
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ (Ξ : Matrix (Fin a₁) C₁ k → ℂ) (Ψ : Matrix A₁ C₁ k → ℂ),
      bigP (haarVol (KO k (Fin a₁))) ϖ σ₁ ν β Ξ = smallP μ₁ σ₁ ν (ν * β) Ψ →
      bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (finCongr ha) eC (gA.val * X * (invT c).val))) =
        smallP μ σ ν (ν * β) fun Y => lam * Ψ (reindex eB eC (gB.val * Y * c.val)) := by
  first | exact @GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | exact GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change | (intros; apply GlobalTheory.FlipMatch.ZMat.bigZeta_eq_smallZeta_change <;> assumption)
