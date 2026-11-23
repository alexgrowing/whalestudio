import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StandardFrameNonsplitMaxCompactInLevel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.One.M.B

def IsPrincipalCongruenceAt {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L) (κ : GAf L n) : Prop :=
  ∀ i j, Valued.v (((s.loc n κ : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))).val - 1) i j) < 1

def FixSph : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S →
    ∀ (s : SplitPlace L), ∀ f ∈ S, f ≠ 0 → (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
    ∀ σ, IsLocS S s σ → GlobalTheory.SmGL.IsSpherical σ.ρ

def FixOne : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S →
    ∀ (s : SplitPlace L), ∀ f ∈ S, f ≠ 0 → (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → IsPrincipalCongruenceAt s κ → NG.rt L n κ f = f) →
    ∀ σ, IsLocS S s σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n)) ≠ ⊥

def LevSplit : Prop := OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (i : Fin (w.st Z).toD7.R.m)
    (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV), StdFrame Y.hF P →
    ∀ s : SplitPlace (w.st Z).toD7.host.E, ∀ κ ∈ Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, TrivOutside {s.v} κ →
      (s.v ∈ gPl (w.st Z).toD7 → IsPrincipalCongruenceAt s κ) →
      P.ψ κ ∈ Formalism.IndefR.Links.levS _ (z.R.toRealDat.βV i)
          (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false)) ∧
        Formalism.IndefR.Lev.levChi _ (z.R.toRealDat.βV i)
          (Formalism.IndefR.RecTie.datVP z.R.toRealDat i (Y.tupT (w.st Z).toD7.what₂.mu0) (z.R.toRealDat.levR z.F.lv2 false))
          (P.ψ κ) = 1

def GoodRef : Prop := ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.LiftRef.AtRows hL fun D _ _ _ _ M =>
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W))
    (hS : NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S), (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real ≠ ⊥ →
    GoodAU (GlobalTheory.LiftRef.autOf (M D.what₂.mu0 j h1 h2) S hS)

end UpperTheory.One.M.B
