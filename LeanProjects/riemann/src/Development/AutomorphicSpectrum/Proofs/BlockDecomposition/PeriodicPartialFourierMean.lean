import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem bT_add_right (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (γ y : hermA D p) :
    bT hn z x (γ + y) = bT hn 0 0 γ + bT hn z x y := by
  apply Subtype.ext
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  ext i j
  simp only [bT, AddSubgroup.coe_add, AddSubgroup.coe_zero, h0, Matrix.add_apply, bl, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp

theorem bT_zero_mem_ratHerm (hn : ρ + p = n) {γ : hermA D p} (hγ : γ ∈ ratHerm D p) :
    bT hn 0 0 γ ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ : γ.1 ∈ ratMx D p p := hγ
  have h0 : adj (0 : Mx D ρ p) = 0 := by
    ext i j
    simp [adj]
  refine (show (bT hn 0 0 γ : hermA D n).1 ∈ ratMx D n n from ⟨bl hn 0 0 0 η, ?_⟩)
  ext i j
  have hij : ∀ a b, (incA D) (η a b) = γ.1 a b := fun a b => by
    rw [← hη]
    rfl
  simp only [bT, AddSubgroup.coe_zero, h0, bl, AddMonoidHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
    simp [hij]

theorem isPer_pm {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ)
    (Φ : hermA D n → ℂ) (hΦ : IsPer Φ) : IsPer (pm hn m ψ b₀ Φ) := by
  intro γ hγ y
  have h : ∀ x z, Φ (bT hn z x (γ + y)) = Φ (bT hn z x y) := fun x z => by
    rw [bT_add_right]
    exact hΦ _ (bT_zero_mem_ratHerm hn hγ) _
  simp only [pm, h]

end GlobalTheory.CompanionTheory.PcFc
