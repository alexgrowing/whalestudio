import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcNb

theorem nzx_mul_nb {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) {nb : hermA D n → G D n} (h : IsNMap nb)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    M.nzx z 0 * (M.nzx 0 x * nb (bT hn 0 0 y)) = nb (bT hn z x y) := by
  rw [← mul_assoc, GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero, zero_add]
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [GlobalTheory.CompanionTheory.PcB.mat_mul', M.nzx_mat, h, h, GlobalTheory.CompanionTheory.PcB.block_unipotent_mul]
  congr 1
  show bl hn z.1 x (adj x) 0 + bl hn (0 : Mx D ρ ρ) 0 (adj 0) y.1 = bl hn z.1 x (adj x) y.1
  rw [GlobalTheory.CompanionTheory.PcB.blockMatrix_add', adj_zero]
  simp

theorem pc_nb : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (F : G D n → ℂ) {nb : hermA D n → G D n}, IsNMap nb → ∀ (g : G D n) (y : hermA D p), pc M m ψ b₀ F (nb (bT hn 0 0 y) * g) = pm hn m ψ b₀ (fun b => F (nb b * g)) y := by
  intro D n ρ p hn M m ψ b₀ F nb h g y
  show ∫ x in m.𝓕, ∫ z in m.𝓖, F (M.nzx z 0 * (M.nzx 0 x * (nb (bT hn 0 0 y) * g))) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ =
    ∫ x in m.𝓕, ∫ z in m.𝓖, F (nb (bT hn z x y) * g) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show F (M.nzx z 0 * (M.nzx 0 x * (nb (bT hn 0 0 y) * g))) * _ = F (nb (bT hn z x y) * g) * _
  rw [← nzx_mul_nb M h z x y]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.PcNb
