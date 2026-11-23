import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem inLat_gl (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ)
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (γ : GL (Fin n) D.host.E) (v : VV ℂ lam) (h : InLat lam w a Λ v) :
    InLat lam w a (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)))
      (rhoVr (tauE D) lam γ v) := by
  obtain ⟨u, s, rfl, hs, ha, hu⟩ := h
  refine ⟨rhoVr (labLL D) lam γ u, s, (TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV lam γ u).symm, hs, ha, ?_⟩
  rw [← map_smul]
  exact TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.nabAtr_map _ lam γ Λ _ hu

theorem UpperTheory.WildA.latMove :
    ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (w : PlL D) (a : ℝ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
      (U : Matrix.unitaryGroup (Fin n) D.host.E) (v : VV ℂ lam),
      InLat lam w a (SDLat.smulLat U.1 Λ) (rhoVr (tauE D) lam (Unitary.toUnits U) v) ↔ InLat lam w a Λ v := by
  intro D n lam w a Λ U v
  have e : SDLat.smulLat U.1 Λ = Λ.map ((Matrix.mulVecLin ((Unitary.toUnits U : GL (Fin n) D.host.E) :
      Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) := rfl
  rw [e]
  generalize (Unitary.toUnits U : GL (Fin n) D.host.E) = γ
  refine ⟨fun h => ?_, inLat_gl D lam w a Λ γ v⟩
  have h2 := inLat_gl D lam w a _ γ⁻¹ _ h
  have e1 : rhoVr (tauE D) lam γ⁻¹ (rhoVr (tauE D) lam γ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have e2 : (Λ.map ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E))).map
      ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = Λ := by
    rw [← Submodule.map_comp]
    have e3 : ((Matrix.mulVecLin ((γ⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)).comp
        ((Matrix.mulVecLin (γ : Matrix (Fin n) (Fin n) D.host.E)).restrictScalars (𝓞 D.host.E)) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show (γ⁻¹).1 *ᵥ (γ.1 *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e3, Submodule.map_id]
  rwa [e1, e2] at h2
