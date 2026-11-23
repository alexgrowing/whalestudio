import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatricesStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem gramSkew_rat {D : D7} (W : HSp D) {ρ : ℕ} (y : Matrix (Fin W.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y) = rat ((-D.host.xi0) • (gramQ W y)ᵀ) := by
  have e : adj (rat y) ⬝ (gA W ⬝ rat y) = rat (gramQ W y) := by
    rw [gramQ, rat_mul, rat_mul, rat_conjTranspose]; rfl
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, e, rat_smul, map_neg]
  rfl

theorem gramQ_eq_of_gramSkew {D : D7} (W : HSp D) {ρ : ℕ} {x y : Matrix (Fin W.rank) (Fin ρ) D.host.E}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat x) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew W (rat y)) : gramQ W x = gramQ W y := by
  rw [gramSkew_rat, gramSkew_rat] at h
  have h' := rat_injective h
  have hξ : -D.host.xi0 ≠ 0 := neg_ne_zero.2 (GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D))
  exact Matrix.transpose_injective (smul_right_injective _ hξ h')

theorem exists_central_ne : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x ≠ gramQ W x₀ → ∃ c : skewA D ρ, star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) ≠ 1 := by
  intro D ψ hψ V V₀ W ρ d x₀ x hne
  by_contra hcon
  push_neg at hcon
  have hall : ∀ c : skewA D ρ, ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) := by
    intro c
    have hn : ‖ψ (d.qS W c (rat x₀))‖ = 1 := hψ.1.2.1 _
    have hs : ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    calc ψ (d.qS W c (rat x)) = ψ (d.qS W c (rat x₀)) * star (ψ (d.qS W c (rat x₀))) * ψ (d.qS W c (rat x)) := by
          rw [hs, one_mul]
      _ = ψ (d.qS W c (rat x₀)) := by rw [mul_assoc, hcon c, mul_one]
  have h := (((GlobalTheory.T.mixedModelCentralTerms_via_gramMatrices D).1 V V₀ W ρ d).2.2 ψ hψ).2.2 (rat x) (rat_mem x) (rat x₀) (rat_mem x₀)
  exact hne (gramQ_eq_of_gramSkew W (h.1 hall))

end GlobalTheory.Unf
