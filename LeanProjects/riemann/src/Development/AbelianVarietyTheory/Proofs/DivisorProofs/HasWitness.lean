import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix

noncomputable section

namespace GlobalTheory.FrameEquiv

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws (DictDat)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}

def HasWitness {r : ℕ} {U : Unf Xo c σ r} (d : DictDat U) : Prop :=
  ∃ Wt : GlobalTheory.Dict.UW (Formalism.L2.PjFree.Unf.ofPj U), (⟨Wt.g, Wt.e, Wt.F, Wt.ik, Wt.φ, d.th⟩ : DictDat U) = d

def GeoSet (W : HSp D) (U : Unf Xo c σ W.rank) (dict : GA D W → Σ k, Frame (U.X k).Ψ W.rank)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  GoodEmb c σ ∧ IsUnf U ∧ 1 ≤ W.rank ∧ l.A = 1 ∧ (∀ k, ModelW W rfl (U.X k)) ∧
    (∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧
    (H.w0 : D.host.E) = GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant.wZero D ∧ (∀ k (τ : D.host.E →+* ℂ), ‖τ (U.X k).ξ0‖ = xiR D) ∧
    (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧ ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom

def AdSet (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (L : GlobalTheory.SW.Lt D.host.E W.rank) (f : WO V W → ℂ)
    (mu : GA D W → ℂ) : Prop :=
  V.gram = 1 ∧ Even V.rank ∧ GlobalTheory.Ker.IsWeak ψ V W om ∧ IsSelfDualC W L ∧ GlobalTheory.Ker.hatV L = Formalism.L2.Pj.latHat W ∧
    IsVacO ψ θ V W (fun _ => 1) s (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E))
      (L : Set (Fin W.rank → D.host.E)) f ∧
    (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ W, mu γ = 1) ∧
    (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.StabLat W k → om (1, k) f = mu k • f) ∧
    ∀ k ∈ GinfC W, (∀ τ, compAt θ τ (Formalism.L2.Theta.mt W k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt W k)) →
      om (1, k) f = (mu k * GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant.vacChar θ W s V.rank (fun _ => 0) k) • f

end GlobalTheory.FrameEquiv

end
