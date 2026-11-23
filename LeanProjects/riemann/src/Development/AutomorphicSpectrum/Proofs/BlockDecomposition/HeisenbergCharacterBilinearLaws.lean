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

variable {D : D7} {ρ p : ℕ}

theorem trA_add (a b : AE D) : trA (a + b) = trA a + trA b := map_add (Algebra.trace (AF D.host.F) (AE D)) a b

theorem pr_add_left (b₀ : HermE D ρ) (x x' y : Mx D ρ p) : pr b₀ (x + x') y = pr b₀ x y + pr b₀ x' y := by
  have h : adj (x + x') = adj x + adj x' := by
    ext i j
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add]
  simp only [pr, h]
  exact Matrix.add_mul _ _ _

theorem pr_add_right (b₀ : HermE D ρ) (x y y' : Mx D ρ p) : pr b₀ x (y + y') = pr b₀ x y + pr b₀ x y' := by
  simp only [pr]
  rw [show (HMul.hMul (b₀.1.map (incA D)) (y + y') : Mx D ρ p) = _ from Matrix.mul_add _ _ _]
  exact Matrix.mul_add _ _ _

theorem chv_add_left (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x x' y : Mx D ρ p) :
    chv ψ b₀ (x + x') y = chv ψ b₀ x y * chv ψ b₀ x' y := by
  simp only [chv, pr_add_left, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_add_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x y y' : Mx D ρ p) :
    chv ψ b₀ x (y + y') = chv ψ b₀ x y * chv ψ b₀ x y' := by
  simp only [chv, pr_add_right, Matrix.trace_add, trA_add, AddChar.map_add_eq_mul]

theorem chv_norm (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    ‖chv ψ b₀ x y‖ = 1 := hψ.2.1 _

theorem chv_zero_right (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (x : Mx D ρ p) : chv ψ b₀ x 0 = 1 := by
  have h : pr b₀ x 0 = 0 := by
    have := pr_add_right b₀ x 0 0
    simpa using this
  simp only [chv, h, Matrix.trace_zero]
  have h0 : trA (0 : AE D) = 0 := map_zero (Algebra.trace (AF D.host.F) (AE D))
  rw [h0, AddChar.map_zero_eq_one]

theorem chv_neg_right (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (x y : Mx D ρ p) :
    chv ψ b₀ x (-y) = conj (chv ψ b₀ x y) := by
  have h1 : chv ψ b₀ x y * chv ψ b₀ x (-y) = 1 := by
    rw [← chv_add_right, add_neg_cancel, chv_zero_right]
  have h2 : chv ψ b₀ x y * conj (chv ψ b₀ x y) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, chv_norm ψ hψ]
    simp
  exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one h1) (h1.trans h2.symm)

theorem trA_incA (t : D.host.E) :
    trA (incA D t) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) := by
  have h2 : Algebra.lmul (AF D.host.F) (AE D) (incA D t) =
      (Algebra.lmul D.host.F D.host.E t).baseChange (AF D.host.F) := by
    ext x
    simp [incA, inclR]
  show Algebra.trace (AF D.host.F) (AE D) (incA D t) = _
  rw [Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem pr_rt (b₀ : HermE D ρ) (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) :
    pr b₀ (rt ξ) (rt ξ') = ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ')).map (incA D) := by
  have h : adj (rt ξ) = ((ξ.map D.sp.cm.sig)ᵀ).map (incA D) := by
    ext i j
    simp only [adj, rt, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  simp only [pr, h, Matrix.map_mul]

theorem chv_rt (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ)
    (ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E) : chv ψ b₀ (rt ξ) (rt ξ') = 1 := by
  have h : Matrix.trace (pr b₀ (rt ξ) (rt ξ')) = incA D (Matrix.trace ((ξ.map D.sp.cm.sig)ᵀ * (b₀.1 * ξ'))) := by
    rw [pr_rt]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rw [chv, h, trA_incA]
  exact hψ.2.2.1 _

theorem chv_continuous (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun v : Mx D ρ p × Mx D ρ p => chv ψ b₀ v.1 v.2) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (trA (D := D)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF D.host.F) (AE D))
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  have ha : Continuous fun v : Mx D ρ p × Mx D ρ p => adj v.1 := by
    unfold adj
    exact ((continuous_fst.matrix_map hc)).matrix_transpose
  refine hψ.1.comp (ht.comp ?_)
  exact (ha.matrix_mul (continuous_const.matrix_mul continuous_snd)).matrix_trace

theorem chv_facts : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, (∀ x x' y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (x + x') y = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x' y) ∧ (∀ x y y' : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (y + y') = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y') ∧ (∀ x y : Mx D ρ p, ‖GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y‖ = 1) ∧ (∀ x y : Mx D ρ p, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (-y) = conj (GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y)) ∧ (∀ ξ ξ' : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ (GlobalTheory.CompanionTheory.FJE.rt ξ) (GlobalTheory.CompanionTheory.FJE.rt ξ') = 1) ∧ Continuous (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.1 v.2) := by
  intro D ρ p ψ hψ b₀
  exact ⟨chv_add_left ψ b₀, chv_add_right ψ b₀, chv_norm ψ hψ b₀, chv_neg_right ψ hψ b₀, chv_rt ψ hψ b₀,
    chv_continuous ψ hψ b₀⟩

end GlobalTheory.CompanionTheory.FJE
