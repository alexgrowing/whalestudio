import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilVacuumFiniteSelfDualLatticeSplitting
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_finite_selfDualLattice_splitting : ∀ (D : D7) (S T : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → S.SigOK → T.SigOK → ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS ∧ UnramAt ε χT) → ∀ (sS : Fam S) (sT : Fam T), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Lt D.host.E S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt S k) ΛS ΛS → GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt T k') ΛT ΛT → ∀ x y : (AE D)ˣ, FinUnit x → FinUnit y → IsDetRoot S k x → IsDetRoot T k' y → om (k, k') f = ((((χT x)⁻¹ * χS y : Circle)) : ℂ) • f := by
  first | exact @GlobalTheory.FinVac.om_vacuum_finite | exact GlobalTheory.FinVac.om_vacuum_finite | (intros; apply GlobalTheory.FinVac.om_vacuum_finite <;> assumption)
