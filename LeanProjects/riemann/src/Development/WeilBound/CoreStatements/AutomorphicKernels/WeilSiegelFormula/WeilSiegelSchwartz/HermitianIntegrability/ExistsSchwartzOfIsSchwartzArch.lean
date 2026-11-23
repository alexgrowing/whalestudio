import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.UntupTupOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhat
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_schwartz_of_isSchwartzArch {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    {a : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (ha : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (F := D.host.F) (E := D.host.E) a) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ, ∀ Y, a Y = f fun τ i j => θ τ (Y j i) := by
  obtain ⟨N, e, he, he', f, hf⟩ := ha
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.SiegelND.SchGlue.exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add]
  let A : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃+ (Fin N → ℝ) := (AddEquiv.mk' Q.toEquiv hadd).symm.trans e
  have hA : Continuous A := he.comp Q.symm.continuous
  have hA' : Continuous A.symm := Q.continuous.comp he'
  let L : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ] (Fin N → ℝ) := A.toRealLinearEquiv hA hA'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun Y => ?_⟩
  have hY : (fun τ i j => θ τ (Y j i)) = Q Y := funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm
  rw [hf, hY]
  show f (e Y) = f (e (Q.symm (Q Y)))
  rw [Homeomorph.symm_apply_apply]

theorem mem_schwartzA_of_sb (θ : InfFam D) (hθ : IsInfFam θ) {m r : ℕ} (Φ : (Fin r → Fin m → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    (fun y : Mx D m r => Φ (untup y)) ∈ schwartzA θ m r := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  choose f hf using fun i => exists_schwartz_of_isSchwartzArch hθ (ha i)
  have hg : ∀ i, (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) := fun i => by
    have h := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) (m := r) (r := m) (g := b i) ⟨(hb i).1, (hb i).2⟩
    exact ⟨h.1, h.2⟩
  have hsum : (fun y : Mx D m r => Φ (untup y)) = ∑ i : Fin k, fun x : Mx D m r =>
      f i (fun τ l j => compAt θ τ x l j) *
        (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j)
          (fun l j => finPart D (x l j)) := by
    funext y
    rw [hs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf]
    rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, _, hg i, rfl⟩

end PositivityTheory.PfWsf.Hand.TupleUntupling
