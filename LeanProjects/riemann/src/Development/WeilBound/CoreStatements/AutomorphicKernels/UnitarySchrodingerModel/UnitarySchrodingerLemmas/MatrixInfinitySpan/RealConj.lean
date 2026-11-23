import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnitary

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwSpan

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS.SwMatch

theorem matInf_map {D : D7} (θ : InfFam D) (τ : D.what₂.Tau) {n : ℕ} (X : Mx D n n) :
    (PositivityTheory.SiegelWeilFormula.Gen.matInf X).map (θ τ) = compAt θ τ X := by
  ext i j
  rfl

theorem aTau_val {D : D7} (θ : InfFam D) {n : ℕ} (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) :
    (aTau θ a τ).1 = compAt θ τ a.1 := rfl

theorem realConj : RealConj := by
  intro D θ hθ n a b
  unfold PositivityTheory.SiegelWeilFormula.Gen.nuInf
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hA : ((aTau θ a τ)⁻¹).1 * compAt θ τ a.1 = 1 := by
    rw [← aTau_val, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have hc : compAt θ τ (conjH a b).1 = compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ := by
    rw [← GlobalTheory.VacKInf.LeviFix.compAt_adj' hθ τ a.1]
    show (a.1 * b.1 * adj a.1).map ((θ τ).comp (infPart D)) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hB : ((aTau θ a τ)⁻¹).1 * (compAt θ τ a.1 * compAt θ τ b.1 * (compAt θ τ a.1)ᴴ) *
      (((aTau θ a τ)⁻¹).1)ᴴ = compAt θ τ b.1 := by
    calc _ = (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1) * compAt θ τ b.1 *
          (((aTau θ a τ)⁻¹).1 * compAt θ τ a.1)ᴴ := by
            rw [Matrix.conjTranspose_mul]
            simp only [Matrix.mul_assoc]
      _ = compAt θ τ b.1 := by rw [hA]; simp
  rw [matInf_map, matInf_map, hc, hB]
  simp

end PositivityTheory.PfSWUS.SwSpan
