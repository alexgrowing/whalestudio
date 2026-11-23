import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.FJE

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem Wz_stronglyMeasurable : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (f : G D n → ℂ), Continuous f → ∀ {X : Type} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (c : X → G D n), Continuous c → StronglyMeasurable fun v => Wz M m ψ b₀ f (c v) := by
  intro D n ρ p hn M m ψ hψ b₀ f hf X _ _ _ _ c hc
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ ρ
  haveI : IsTopologicalAddGroup (Mx D ρ ρ) := i1
  haveI : LocallyCompactSpace (Mx D ρ ρ) := i2
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : T2Space (Mx D ρ ρ) := i4
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D ρ) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D ρ) :=
    (GlobalTheory.CompanionTheory.FourierN.isClosed_hermA (D := D) (n := ρ)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := m.hz.1
  haveI : SFinite m.lz := inferInstance
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hcont : Continuous fun u : X × hermA D ρ => f (M.w * M.nzx u.2 0 * c u.1) * conj (chz ψ b₀ u.2) := by
    refine (hf.comp ((continuous_const.mul ?_).mul (hc.comp continuous_fst))).mul (hchz.comp continuous_snd)
    exact M.nzx_cont.comp (continuous_snd.prodMk continuous_const)
  exact hcont.stronglyMeasurable.integral_prod_right

end GlobalTheory.CompanionTheory.FJE
