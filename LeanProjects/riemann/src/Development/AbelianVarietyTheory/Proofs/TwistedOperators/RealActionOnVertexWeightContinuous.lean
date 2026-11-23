import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RealActCont

theorem realAct_inv_continuous : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (θ : InfFam D), IsInfFam θ →
    ∀ (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (Λ : Module.Dual ℂ (VV ℂ (wt G X))) (w : VV ℂ (wt G X)),
    Continuous fun k : GinfC (G.V X) => Λ (realAct θ fr X ((k : GA D (G.V X))⁻¹) w) := by
  intro D T L sc G θ hθ fr X Λ w
  classical
  obtain ⟨hc, -⟩ := GlobalTheory.CoefModel.realGL_laws hθ (G.V X)
  have hG : ∀ _τ : D.what₂.Tau, (1 : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).PosDef := fun _ => Matrix.PosDef.one
  let A : GinfC (G.V X) → D.what₂.Tau → GL (Fin (G.V X).rank) ℂ :=
    fun k => invTrK (realIn θ fr X ((k : GA D (G.V X))⁻¹))
  have hA : ∀ τ, Continuous fun k => (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) := by
    intro τ
    have e : ∀ k : GinfC (G.V X), (A k τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) =
        Matrix.transpose ((((frGL fr X τ)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ) *
          Formalism.L2.Pj.archM (G.V X) (θ τ) (k : GA D (G.V X)) * (frGL fr X τ : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ)) := by
      intro k
      simp only [A, map_inv]
      show ((((realIn θ fr X (k : GA D (G.V X)) τ)⁻¹)⁻¹ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).transpose = _
      rw [inv_inv]
      simp [realIn, MulAut.conj_apply, GlobalTheory.CoefModel.realGL_coe]
    refine Continuous.congr ?_ fun k => (e k).symm
    exact ((continuous_const.mul ((hc τ).comp continuous_subtype_val)).mul continuous_const).matrix_transpose
  have key := GlobalTheory.CoefModel.continuous_rhoH (wt G X) hG A hA (GlobalTheory.CoefModel.toHilb (wt G X) hG w)
  have hΛ : Continuous (Λ ∘ₗ (GlobalTheory.CoefModel.toHilb (wt G X) hG).symm.toLinearMap) :=
    LinearMap.continuous_of_finiteDimensional _
  refine (hΛ.comp key).congr fun k => ?_
  simp only [Function.comp_apply, GlobalTheory.CoefModel.rhoH_toHilb, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.RealActCont
