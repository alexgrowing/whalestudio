import Formalism.LocalToGlobal.InertKernelTheory.FrameLatMap
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepTwLat

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Defs

variable (D : D7)

def IntAtP (p : ℕ) (e : D.host.E) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def FractionalIdealIntegralAtP (p : ℕ) : Prop :=
  ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), IntAtP D p a

def hStd {N : ℕ} (x y : Fin N → D.host.E) : D.host.E := ∑ k, D.host.conj (x k) * y k

def SelfDualP (p : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, IntAtP D p (hStd D x y)) ∧
  ∀ y : Fin N → D.host.E, (∀ x ∈ L, IntAtP D p (hStd D x y)) → ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • y ∈ L

def MapsAtP (p : ℕ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (A *ᵥ x) ∈ L'

def locSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun x : Fin N → D.host.E => fun k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

end Defs

section Ties

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def KerLatW (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ v : X.Pl,
      locSpan D (X.G.P.W v) (ρ v) (large₂ j L0 La') =
        (X.latAt v j L0.2).map (((M j L0 v).mulVecLin).restrictScalars (X.G.P.W v)) ∧
      locSpan D (X.G.P.W v) (ρ v) (Lg' j L0 La') =
        (X.latAt v (j + 1) La'.2).map (((M (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))

def SelfDualTie : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    SelfDualP D p (large₂ j L0 La') ∧ SelfDualP D p (Lg' j L0 La')

end Ties

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

end Glob

section Loc

variable (D : D7) {p : ℕ} {N N' : ℕ}

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

end Loc

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

def KerLatWF (fd : Formalism.L2.PairingIndexBounds.F.FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  KerLatW X hfin D fd.frM (fun j L0 _ => fd.kerN j L0) (fun j _ La' => fd.kerN (j + 1) La') ρ

def SelfDualF (fd : Formalism.L2.PairingIndexBounds.F.FData X D) : Prop :=
  SelfDualTie X hfin D (fun j L0 _ => fd.kerN j L0) (fun j _ La' => fd.kerN (j + 1) La')

end Main

end Formalism.L2.KerInert.RepTwLat

set_option pp.fullNames true
