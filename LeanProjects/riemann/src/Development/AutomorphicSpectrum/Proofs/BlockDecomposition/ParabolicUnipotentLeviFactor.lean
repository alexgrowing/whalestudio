import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelNM
open GlobalTheory.StdUnn.Model

theorem unip_mul_levi : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
    ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  intro D p q hq a ha
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  obtain ⟨m', hm'⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) (n := p) a⁻¹
  rw [inv_inv] at hm'
  have hmm : m * m' = 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_one, hm, hm',
      GlobalTheory.StdUnn.LeftInvSect.levi_mul_inv])
  have hmm' : m' * m = 1 := by
    rw [eq_inv_of_mul_eq_one_right hmm, inv_mul_cancel]
  have h2 : (adj (a⁻¹).1 : Mx D p p) * adj a.1 = 1 := by
    rw [← adj_mul]; simp [adj_one]
  refine ⟨m * u * m', m, a.1 * b * adj a.1, ?_, ?_, hm⟩
  · rw [mul_assoc (m * u), hmm', mul_one, e]
  · rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm, hu, hm']
    simp [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, h2, -Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.SiegelNM
