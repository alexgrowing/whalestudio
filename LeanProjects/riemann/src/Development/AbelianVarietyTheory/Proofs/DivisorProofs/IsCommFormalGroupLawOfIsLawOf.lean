import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoordStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfEvalCubeLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupFormalLawCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

def firstFactor (A : Type) [CommRing A] [Bialgebra k A] : A ⊗[k] A →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp (Bialgebra.counitAlgHom k A))
    (fun _ _ => Commute.all _ _)

theorem firstFactor_comul (A : Type) [CommRing A] [Bialgebra k A] (a : A) :
    firstFactor A (Coalgebra.comul (R := k) a) = a := by
  have h : (firstFactor A).toLinearMap =
      (TensorProduct.rid k A).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).lTensor A := by
    apply TensorProduct.ext'
    intro a b
    simp [firstFactor, Algebra.smul_def, mul_comm]
  have := LinearMap.congr_fun h (Coalgebra.comul (R := k) a)
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.Katz.Chart

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem firstFactor_ev₂ (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) k) :
    firstFactor (G.A n) (c.ev₂ n f) =
      c.ev n (at2 f (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0)) := by
  have hy : ∀ j : Fin d ⊕ Fin d, IsNilpotent ((Sum.elim (c.x n) (fun _ => (0 : G.A n))) j) := by
    intro j; cases j with
    | inl i => exact c.nil n i
    | inr i => exact IsNilpotent.zero
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n) (firstFactor (G.A n))
    (c.x₂ n) (c.nil₂ n) _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.x₂, firstFactor]
      | inr i => simp [Chart.x₂, firstFactor, c.aug]) f
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n)).1 (Fin d) (c.ev n)
    (fun t => by rw [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c.nil n t)
    (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0))
    (by intro j; cases j with
      | inl i => exact constantCoeff_X i
      | inr i => exact map_zero _)
    _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]
      | inr i => simp) f
  exact h2.trans h1.symm

end GlobalTheory.Katz.Chart

namespace GlobalTheory

theorem Katz.Chart.isLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  intro p k _ d G c μ hμ
  have hcomp : ∀ (n : ℕ) (i : Fin d), pullbackTwo (G.res n) (Coalgebra.comul (R := k) (c.x (n + 1) i))
      = Coalgebra.comul (R := k) (c.x n i) := fun n i => by
    rw [pullTwo_comul, c.res]
  refine ⟨((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1, ?_, ?_, ?_⟩
  · funext i
    obtain ⟨f, -, huniq⟩ := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2 (fun n => c.x n i) (fun n => c.res n i)
    have hX : ∀ n, c.ev n (X i) = c.x n i := fun n => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ i
    have hA : ∀ n, c.ev n (op μ (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0) i) =
        c.x n i := fun n => by
      rw [op, ← firstFactor_ev₂, hμ, firstFactor_comul]
    exact (huniq _ hA).trans (huniq _ hX).symm
  · intro i
    obtain ⟨s, -, huniq⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => hcomp n i)
    have h1 : ∀ n, c.ev₂ n (Katz.swap (μ i)) = Coalgebra.comul (R := k) (c.x n i) := fun n => by
      rw [((GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c) n).2.2.1, hμ, Coalgebra.comm_comul]
    exact (huniq _ h1).trans (huniq _ (fun n => hμ n i)).symm
  · funext i
    have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
      (op μ (op μ x1 x2) x3 i - op μ x1 (op μ x2 x3) i) (fun n h => by
        rw [map_sub, ((GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n h).2 i), sub_self])
    exact sub_eq_zero.1 hinj

end GlobalTheory
