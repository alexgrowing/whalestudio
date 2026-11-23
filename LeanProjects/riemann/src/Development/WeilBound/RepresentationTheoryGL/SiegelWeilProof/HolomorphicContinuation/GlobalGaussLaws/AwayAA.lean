import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetSumEqSumCellSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

def cθ (θ : InfFam D) (τ : D.what₂.Tau) : AE D →+* ℂ := (θ τ).comp (infPart D)

theorem compAt_eq {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (w : Mx D m k) : compAt θ τ w = w.map (cθ θ τ) := rfl

theorem compAt_mul' {θ : InfFam D} {τ : D.what₂.Tau} {m k l : ℕ} (x : Mx D m k) (y : Mx D k l) :
    compAt θ τ (x * y : Mx D m l) = compAt θ τ x * compAt θ τ y := by
  simp only [compAt_eq]; exact Matrix.map_mul

theorem compAt_one' {θ : InfFam D} {τ : D.what₂.Tau} {k : ℕ} : compAt θ τ (1 : Mx D k k) = 1 := by
  simp only [compAt_eq]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_zero' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} : compAt θ τ (0 : Mx D m k) = 0 := by
  ext i j; simp [compAt_eq]

theorem compAt_add' {θ : InfFam D} {τ : D.what₂.Tau} {m k : ℕ} (x y : Mx D m k) :
    compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y := by
  ext i j; simp [compAt_eq]

theorem component_block_matrix {θ : InfFam D} {τ : D.what₂.Tau} (a b c d : Mx D n n) :
    compAt θ τ (blk4 a b c d : Mx D (n + n) (n + n)) = blk4 (compAt θ τ a) (compAt θ τ b) (compAt θ τ c) (compAt θ τ d) :=
  GlobalTheory.StdUnn.Frame.block_matrix_map _ a b c d

theorem ae_ext {θ : InfFam D} (hθ : IsInfFam θ) {z z' : AE D} (h1 : ∀ τ, cθ θ τ z = cθ θ τ z')
    (h2 : finPart D z = finPart D z') : z = z' := by
  have h := (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.2.2 (z - z') (fun τ => by
      have := h1 τ
      simp only [cθ, RingHom.comp_apply] at this
      rw [RingHom.map_sub, RingHom.map_sub, this, sub_self])
    (by rw [RingHom.map_sub, h2, sub_self])
  exact sub_eq_zero.mp h

theorem mx_ext {θ : InfFam D} (hθ : IsInfFam θ) {m k : ℕ} {x x' : Mx D m k} (h1 : ∀ τ, compAt θ τ x = compAt θ τ x')
    (h2 : x.map (finPart D) = x'.map (finPart D)) : x = x' := by
  ext i j
  exact ae_ext hθ (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)

theorem cθ_cA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : AE D) : cθ θ τ (cA D z) = conj (cθ θ τ z) :=
  (GlobalTheory.StdUnn.RealComp.real_components D θ hθ).2.1 z τ

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) z) =
    (Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) z)
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
  rfl

end PositivityTheory.Rg.Sw.Glob.AW
