import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem adj_herm {D : D7} {ρ : ℕ} (b₀ : HermE D ρ) :
    adj (b₀.1.map (incA D) : Mx D ρ ρ) = b₀.1.map (incA D) := by
  have h := rat_conjTranspose b₀.1
  have e : b₀.1ᴴ = b₀.1 := b₀.2
  rw [e] at h
  exact h.symm

theorem chz_jc {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p) :
    chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  set B : Mx D ρ ρ := b₀.1.map (incA D) with hB
  have hadj : adj B = B := adj_herm b₀
  have e1 : Matrix.trace (B * (y * adj x)) = Matrix.trace (pr b₀ x y) := by
    show _ = Matrix.trace (adj x * (B * y))
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : Matrix.trace (B * (x * adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← GlobalTheory.CompanionTheory.FourierN.trace_adj]
    have h : adj (pr b₀ x y) = HMul.hMul (HMul.hMul (adj y) B : Mx D p ρ) x := by
      show adj (HMul.hMul (adj x) (HMul.hMul B y : Mx D ρ p) : Mx D p p) = _
      rw [adj_mul, adj_mul, adj_adj, hadj]
    rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc x, Matrix.trace_mul_comm]
  have e3 : Matrix.trace (HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 : Mx D ρ ρ) =
      Matrix.trace (pr b₀ x y) + cA D (Matrix.trace (pr b₀ x y)) := by
    show Matrix.trace (B * (y * adj x + x * adj y)) = _
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2]
  rw [chz, show HMul.hMul (b₀.1.map (incA D)) (GlobalTheory.CompanionTheory.FJE.jc y x).1 = HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 from rfl, e3,
    GlobalTheory.CompanionTheory.FourierN.halfTr_add_cA]
  rfl

end GlobalTheory.CompanionTheory.FJE
