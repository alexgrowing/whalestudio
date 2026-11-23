import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsPairMass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumReads
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralPointsFixAdelicClassicalVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairsStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacMoveFin

theorem mulStep : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  ∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀ x₁ y₁ g₁ h₁ x₂ y₂ g₂ h₂ c₁ c₂ hg₁ hh₁ hg₂ hh₂ hr₁ hr₂
  have he := GlobalTheory.NormSum.Model.vac_mem_TT hSet.crv hodd.1
  have hG := GlobalTheory.NormSum.RatExtend.TT_smul c₂ (W.maps x₂ y₂ e0 he)
  have key := GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hodd.1 x₁ y₁ g₁ h₁ hg₁ hh₁ c₁ f₀ hf₀ hr₁ _ hG _ hr₂
  have h1 : om (g₁ * g₂, h₁ * h₂) f₀ = om (g₁, h₁) (om (g₂, h₂) f₀) := by
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  have h2 : (c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0 = c₁ • W.Om x₁ y₁ (c₂ • W.Om x₂ y₂ e0) := by
    rw [W.smul _ _ _ _ (W.maps x₂ y₂ e0 he), ← W.mul _ _ _ _ _ he, smul_smul]
  rw [h1, h2]; exact key

theorem vacuum_move_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT x y g h hg hh f₀ hf₀
  exact GlobalTheory.T.movedVacuum_constant_trivial_finite_pairs ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀
    (GlobalTheory.VacLine.moved_vacuum_reads ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (mulStep ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.SplitVacMove.reads_om_split ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀)
    (GlobalTheory.T.inertIntegralPoints_fix_adelic_classical_vacuum ψ θ S T hS hT cc δ r hSet e0 W χS χT om hW hInp t0 ht0 hev hodd hfS hfT f₀ hf₀) x y g h hg hh

end GlobalTheory.VacMoveFin
