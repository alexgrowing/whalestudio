import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas : ∀ (D : D7) (A V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (WO A V)) (𝓨 : Set (WO A V)), IsCovolOne (ratL V A) ν 𝓨 → ∀ ω : G D A.rank →* Module.End ℂ (schwartzA θ V.rank A.rank), IsWeilSch ψ χ θ V ν ω → ∃ (ψ₀ : AddChar (AF D.host.F) ℂ) (μ : D.host.E) (lam : D.host.F) (κ : GA D (dblSp A) ≃* G D A.rank) (omh : GA D (dblSp A) × GA D V →* Module.End ℂ (WO (dblSp A) V → ℂ)), IsStdChar D ψ₀ (-1) ∧ IsSkew μ ∧ algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ ψ = shift ψ₀ lam ∧ IsChart A μ κ ∧ IsWeilDatumO ψ₀ (dblSp A) V 1 χ⁻¹ omh ∧ IsTransport ψ₀ θ A V ν 𝓨 omh κ ω := by
  first | exact @GlobalTheory.StdUnn.SchDatum.exists_datum | exact GlobalTheory.StdUnn.SchDatum.exists_datum | (intros; apply GlobalTheory.StdUnn.SchDatum.exists_datum <;> assumption)
