import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToTWsmallZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteLiftZfin

open Matrix

theorem isCuspFun_of_posDef {D : D7} {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) (φ : GA D V → ℂ) :
    IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hτ : ∀ a, tauE D τ0 (star a) = starRingEnd ℂ (tauE D τ0 a) := D.sp.cm.cmUnram.2.1 (tauE D τ0)
  have h1 := congrArg (tauE D τ0) (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have hx : star (fun i => tauE D τ0 (C i ⟨0, hr⟩)) ⬝ᵥ (gramAt D V τ0 *ᵥ fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]
    simp only [gramAt, Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm
  have h2 : (fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    by_contra hne
    have := (hV τ0).dotProduct_mulVec_pos hne
    rw [hx] at this
    exact lt_irrefl _ this
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact (tauE D τ0).injective ((congrFun h2 i).trans (map_zero (tauE D τ0)).symm)

theorem lift_zfin : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ →
    (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
    IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧
      (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 hP hω hθ hΦ hS _ hH hF hφ
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  exact (hK.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ ⟨hφ, isCuspFun_of_posDef hS φ⟩ ⟨Φ, hΦ⟩).2.zfin

end GlobalTheory.DefiniteLiftZfin
