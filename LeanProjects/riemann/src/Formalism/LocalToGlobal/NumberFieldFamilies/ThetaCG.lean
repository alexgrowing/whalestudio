import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCS
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCT

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GelfAd (D : D7) : Prop := ∀ (V : HSp D) (τ : D.what₂.Tau) (n : ℕ), ∀ k ∈ GinfC V, ∀ f : GA D V → ℂ, Smo (th0 D) V f →
  gelf (th0 D) V τ n (rTr V k f) = rTr V k (gelf (th0 D) V τ n f)

def ZFin {D : D7} (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf (th0 D) V τ k f ∈ W

def ZFinConj (D : D7) : Prop := ∀ (V : HSp D) (φ : GA D V → ℂ), Smo (th0 D) V φ → ZFin V φ → ZFin V (star φ)

variable {D : D7} {V : HSp D}

def adI (k : GA D V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  infMat D.sp.cm.sig V.gram (th0 D τ) k⁻¹ * X * infMat D.sp.cm.sig V.gram (th0 D τ) k

def CoCpt (N : Subgroup (GA D V)) : Prop :=
  ∃ K : Set N, IsCompact K ∧ ∀ n : N, ∃ γ : (GQ V).subgroupOf N, γ • n ∈ K

def NICpt (D : D7) : Prop := ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → CoCpt (NI V C)

end Formalism.L2.Fam.ThC

end
