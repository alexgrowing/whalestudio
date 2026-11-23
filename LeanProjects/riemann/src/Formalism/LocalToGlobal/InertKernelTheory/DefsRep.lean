import Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
import Formalism.LocalToGlobal.InertKernelTheory.StatementBeCob
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.PairingIndexBounds.PendingAdmissibility.LocalFDerivAdmissibility.RepRed

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

def CurveAt (l : ℕ) [Fact l.Prime] (be : MvPowerSeries (Fin 2) (K0 l)) (g2 g3 ε s2 : MaximalUnramifiedExtension l) : Prop :=
  ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    MvPowerSeries.constantCoeff be = 0 ∧
    ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))

def OrthInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]) : Prop :=
  ∃ (r : ℕ) (Θ : MvPowerSeries (Fin r) ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (f f' : ι → Fin r → MaximalUnramifiedExtension l),
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsHypPair σ f f' ∧ Th = MvPowerSeries.subst (hypLin l f f') Θ ∧
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[l]) *
      @inParamK l _ (Fin r) ℂ_[l] _ (wittFractionAlgebraCp l) Θ)

def OrthAll {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', OrthInt p g2 g3 s2 ε (thA ℂ_[p] φ (thFOf X pos F j L0 La'))

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

def CombAt (T : Tor D) (e : FamE D) (lam : Qbar →+* ℂ_[p]) : Prop :=
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    admitted D _ _ (large₂ j L0 La') (Lg' j L0 La') ∧ IsComb D T e lam (large₂ j L0 La') (Lg' j L0 La') (F j L0 La')

def FrameHyp (S : ∀ j, X.Lt j → X.Lt (j + 1) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) →
      (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) → ℂ_[p])
    (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p]) : Prop :=
  letI := wittFractionAlgebraCp p
  letI := Formalism.L2.G.Pend.algKfC E.toCEmb
  ∀ j (L0 : X.Lt j), L0 ∈ Formalism.L2.G.Pend.repOf X.Lv hfin j → ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ φ : Frm X j L0 La', ∃ (r : ℕ) (b : Fin r → Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E),
      LocBasis D p (YYl D (large₂ j L0 La') (Lg' j L0 La')) b ∧ Orthonormal D b ∧
      ∃ (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (f f' : X.EA j → Fin r → MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsHypPair σ f f' ∧
        thA ℂ_[p] φ (thFOf X pos (fun j La La' => linSub (S j La La') (F j La La')) j L0 La') =
          MvPowerSeries.subst (hypLin p f f') (thOrth D lam c b (F j L0 La'))

end Glob

def DictInt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (c : ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    Formalism.MainNotions.TaylorLogMetric.IsModel lam Λ C ∧ Formalism.MainNotions.TaylorLogMetric.IsWq (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq ∧
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
      (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      Formalism.MainNotions.TaylorLogMetric.IntegralMv (Formalism.MainNotions.TaylorLogMetric.atLog D lam Λ C wq b G * Formalism.MainNotions.TaylorLogMetric.ePh lam Λ C wq r) →
      Integral (mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[p]) *
        @inParamK p _ (Fin r) ℂ_[p] _ (wittFractionAlgebraCp p) (thOrth D lam c b G))

end Formalism.L2.KerInert.Rep
