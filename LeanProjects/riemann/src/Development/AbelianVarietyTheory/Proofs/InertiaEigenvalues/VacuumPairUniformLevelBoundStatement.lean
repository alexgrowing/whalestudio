import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumPairUniformLevelBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_pair_uniform_level_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  first | exact @GlobalTheory.LevelFourier.smul_mem_trSp | exact GlobalTheory.LevelFourier.smul_mem_trSp | (intros; apply GlobalTheory.LevelFourier.smul_mem_trSp <;> assumption)
