import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heisO_add_fun (S T : HSp D) (u : WO S T) (G H : WO S T → ℂ) :
    heisO ψ S T u (G + H) = heisO ψ S T u G + heisO ψ S T u H := by
  funext w
  simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_smul_fun (S T : HSp D) (u : WO S T) (c : ℂ) (G : WO S T → ℂ) :
    heisO ψ S T u (c • G) = c • heisO ψ S T u G := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem integrableOn_heisO (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (u a : WO V W) :
    IntegrableOn (fun z => heisO ψ V W u G (isoPart V W C z + a)) 𝓨 μ := by
  obtain ⟨-, -, hvol⟩ := h
  obtain ⟨c, hc⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hcont : Continuous (fun z => heisO ψ V W u G (isoPart V W C z + a)) :=
    (GlobalTheory.HeisOrtho.continuous_heisO hψ.1 hG.cont u).comp ((continuous_isoPart V W C).add continuous_const)
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound hcont.aestronglyMeasurable c (Filter.Eventually.of_forall fun z => ?_)
  rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  exact hc _

theorem term_linear : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h y
  have key : ∀ G, IsThetaFunO ψ V W G → IntegrableOn
      (fun z => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G (isoPart V W C z + midPart V V' W B 0)) 𝓨 μ :=
    fun G hG => integrableOn_heisO V W C hψ h hG _ _
  refine ⟨fun G H hG hH => ?_, fun c G hG => ?_⟩
  · simp only [term, res, heisO_add_fun, Pi.add_apply]
    exact integral_add (key G hG) (key H hH)
  · simp only [term, res, heisO_smul_fun, Pi.smul_apply, smul_eq_mul]
    first
      | exact integral_const_mul c _
      | exact integral_mul_left c _

end GlobalTheory.MixedTerm

end
