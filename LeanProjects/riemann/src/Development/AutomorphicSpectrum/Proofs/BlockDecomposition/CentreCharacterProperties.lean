import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.CentralChar

theorem chz_facts : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
    (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧
      (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  intro D ρ ψ hψ b₀
  refine ⟨fun z z' => ?_, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀, fun z hz => ?_, GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀⟩
  · have e : (HMul.hMul (b₀.1.map (incA D)) (z + z').1 : Mx D ρ ρ) =
        (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) + (HMul.hMul (b₀.1.map (incA D)) z'.1 : Mx D ρ ρ) :=
      Matrix.mul_add _ _ _
    have hadd : ∀ a c : AE D, halfTr (a + c) = halfTr a + halfTr c := fun a c => by
      simp only [halfTr, trA, map_add, mul_add]
    unfold chz
    rw [e, Matrix.trace_add, hadd, AddChar.map_add_eq_mul]
  · obtain ⟨Z, hZ⟩ := hz
    have hZ' : Z.map (incA D) = z.1 := hZ
    have e : Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) = incA D (Matrix.trace (b₀.1 * Z)) := by
      rw [← hZ', ← Matrix.map_mul]
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    unfold chz
    rw [e, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA]
    exact hψ.2.2.1 _

end GlobalTheory.CompanionTheory.FJE.CentralChar
