import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_fold {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ) (hP : Integrable P m.μ) :
    ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D ρ p
  have : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  have : Countable (ratMx D ρ p) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hμ := m.hμ
  have := hμ.1
  let e : Matrix (Fin ρ) (Fin p) D.host.E ≃ ratMx D ρ p :=
    Equiv.ofBijective (fun ξ => ⟨rat ξ, rat_mem ξ⟩)
      ⟨fun a b h => rat_injective (congrArg Subtype.val h), fun g => by
        obtain ⟨ξ, hξ⟩ := mem_ratMx.1 g.2
        exact ⟨ξ, Subtype.ext hξ⟩⟩
  have h1 : ∀ y, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) =
      ∑' g : ratMx D ρ p, P (g +ᵥ y) := fun y => e.tsum_eq fun g => P (g +ᵥ y)
  simp only [h1]
  rw [hμ.2.1.integral_eq_tsum'' P hP]
  refine (integral_tsum (ι := ratMx D ρ p) (f := fun g y => P (g +ᵥ y)) (fun g => ?_) ?_).symm
  · exact ((hP.comp_add_left (g : Mx D ρ p)).aestronglyMeasurable).restrict
  · rw [← hμ.2.1.lintegral_eq_tsum'' fun x => ‖P x‖ₑ]
    exact hP.2.ne

end GlobalTheory.CompanionTheory.FJE
