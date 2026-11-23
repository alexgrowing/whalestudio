import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def tLab (n k : ℕ) : List ℤ := List.replicate k 1 ++ List.replicate (n - k) 0

abbrev Pt (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ

variable (D) in

def SplitOff (S₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  w.under (𝓞 D.host.F) ∉ S₀ ∧ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))

def IsEigSplit (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV i t).H) (S₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : Pt D) (z : (R.HV i t).H) : Prop :=
  ∀ w, SplitOff D S₀ w → ∀ k, 1 ≤ k → k ≤ (Vc D i).rank →
    h w (Finsupp.single (tLab (Vc D i).rank k) 1) z = x w k • z

def PtHasString (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (x : Pt D) : Prop :=
  ∀ w, SplitOff D S₀ w → ∃ B : Multiset ℂˣ, B.card = (Vc D i).rank ∧
    (∀ k, 1 ≤ k → k ≤ (Vc D i).rank → x w k = GlobalTheory.LFun.satEig (Ideal.absNorm w.asIdeal) (Vc D i).rank B k) ∧
    GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV R i t w : ℂ) D.R.t ≤ B.map fun a : ℂˣ => (a : ℂ)

def PtString (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ h, GlobalTheory.Hk3.IsOpsV R i t h →
  ∀ S₀ : Finset (HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ⊆ S₀ →
  ∀ (x : Pt D) (y : (R.HV i t).H), y ≠ 0 → IsEigSplit R i t h S₀ x y → PtHasString R i t S₀ x →
    ∃ s : GlobalTheory.DownLift.Sys D,
      (∀ z : (R.HV i t).H, IsEigSplit R i t h S₀ x z ↔ GlobalTheory.DownLift.IsEigV R i t h s z) ∧
      GlobalTheory.DownLift.HasString R i t s

def PtStringAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → ∀ i t, PtString R i t

example : tLab 4 1 = [1, 0, 0, 0] := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.EigenSplitStrings

end
