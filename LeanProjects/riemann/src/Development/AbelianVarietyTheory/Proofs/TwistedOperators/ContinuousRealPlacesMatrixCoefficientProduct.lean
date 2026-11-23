import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReindexUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefCont

theorem continuous_coefR : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  intro D θ hθ V S M v a
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  unfold coefR
  refine continuous_finset_prod _ fun τ _ => ?_
  have hc : Continuous fun g : GA D V => cmp θ τ g := GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)
  have hu : ∀ g : GA D V, (cmp θ τ g)ᴴ * gramAt D V τ * cmp θ τ g = gramAt D V τ := by
    intro g
    have h0 := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram (tauE D τ)
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x) (θ τ) (hθ τ) g
    have he : (cmp θ τ g)ᴴ = ((cmp θ τ g).map (starRingEnd ℂ)).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he]
    exact h0
  have hB : M.fr τ * (M.fr τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hmem : ∀ g : GA D V, Formalism.REAL.inUJ (M.ε τ) (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) := by
    intro g
    unfold Formalism.REAL.inUJ
    calc (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)
        = ((M.fr τ)⁻¹)ᴴ * ((cmp θ τ g)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * cmp θ τ g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
          rw [M.fr_gram τ, hu g]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) := by
          rw [hB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hconj : Continuous fun g : GA D V => M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have hσ := (M.ds τ).2.2.1.2.2 (a τ)
  have hrep : Continuous fun g : GA D V => M.rep τ (cmp θ τ g) (a τ) :=
    hσ.comp_continuous hconj hmem
  exact continuous_const.inner hrep

end GlobalTheory.SepPer.CoefCont
