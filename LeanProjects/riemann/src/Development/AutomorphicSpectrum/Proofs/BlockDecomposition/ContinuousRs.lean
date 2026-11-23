import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

def rs (σ : (D.what₂.Tau → ℂ) →+ AE D) (s : ℝ) : AE D := σ fun _ => (s : ℂ)

theorem rs_add (σ : (D.what₂.Tau → ℂ) →+ AE D) (s t : ℝ) : rs σ (s + t) = rs σ s + rs σ t := by
  unfold rs
  rw [← map_add]
  congr 1
  funext τ
  simp

theorem rs_zero (σ : (D.what₂.Tau → ℂ) →+ AE D) : rs σ 0 = 0 := by
  unfold rs
  have : (fun _ : D.what₂.Tau => ((0 : ℝ) : ℂ)) = 0 := by funext; simp
  rw [this, map_zero]

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem cA_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (s : ℝ) :
    cA D (rs σ s) = rs σ s := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [RingHom.map_sub, finPart_cA, h0, map_zero, sub_zero]
  · have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
    rw [RingHom.map_sub, RingHom.map_sub, GlobalTheory.PhaseReal.infPart_cA,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hσ.inf τ)]
    unfold rs
    rw [hσ.comp]
    simp

theorem continuous_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    Continuous (rs σ) :=
  hσ.cont.comp (continuous_pi fun _ => Complex.continuous_ofReal)

def path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ℝ →+ hermA D r where
  toFun s := ⟨rs σ s • a.1.map (incA D), by
    show adj (rs σ s • a.1.map (incA D)) = rs σ s • a.1.map (incA D)
    rw [adj_smul, cA_rs hσ]
    congr 1
    exact GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA a⟩
  map_zero' := by
    apply Subtype.ext
    show rs σ 0 • a.1.map (incA D) = 0
    rw [rs_zero, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    show rs σ (s + t) • a.1.map (incA D) = rs σ s • a.1.map (incA D) + rs σ t • a.1.map (incA D)
    rw [rs_add, add_smul]

def lam (θ : InfFam D) (α : D.host.F) (t : AE D) : ℝ :=
  -∑ τ, (θ τ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re

def multM (θ : InfFam D) (α : D.host.F) (V : HSp D) (a : HermE D r) (y : Mx D V.rank r) : ℝ :=
  lam θ α (Matrix.trace (HMul.hMul (a.1.map (incA D)) (inner V y y) : Mx D r r))

def pairF (θ : InfFam D) (α : D.host.F) (a β : HermE D r) : ℝ :=
  lam θ α (incA D (Matrix.trace (β.1 * a.1)))

end GlobalTheory.CompanionTheory.WSum
