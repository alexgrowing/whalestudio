import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem kFin_le_sm (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ M.sm τ := by
  intro w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  exact (GlobalTheory.SmoothCyclic.sm_eq M τ).ge (h.2.2.1 w hw)

theorem tprod_eq_zero_of_kFin_off (hHC : GlobalTheory.Published.HarishChandraModules) {D : D7} {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) (hΛ : SepCont M Λ)
    (h0 : ∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) (s : Finset D.what₂.Tau) :
    ∀ v : M.Vec, (∀ τ, τ ∉ s → IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)) → Λ (PiTensorProduct.tprod ℂ v) = 0 := by
  induction s using Finset.induction_on with
  | empty => exact fun v hv => h0 v fun τ => hv τ (Finset.notMem_empty τ)
  | insert a s ha ih =>
    intro v hv
    obtain ⟨ℓ, hℓ, hℓv⟩ := hΛ a v
    have hk : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M a, ℓ w = 0 := by
      intro w hw
      rw [hℓv ⟨w, kFin_le_sm hHC M a hw⟩]
      refine ih _ fun τ hτ => ?_
      by_cases e : τ = a
      · subst e
        rw [Function.update_self]
        exact hw
      · rw [Function.update_of_ne e]
        exact hv τ (by simp [e, hτ])
    have := GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M a ℓ hℓ hk (v a) (v a).2
    rw [hℓv (v a), Function.update_eq_self] at this
    exact this

theorem eq_zero_of_sepCont : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := by
  intro hHC D V S M Λ hΛ h0
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.zero_apply]
  exact tprod_eq_zero_of_kFin_off hHC M Λ hΛ h0 Finset.univ v fun τ hτ => absurd (Finset.mem_univ τ) hτ

example : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ), SepCont M Λ → (∀ v : M.Vec, KVecP M v → Λ (PiTensorProduct.tprod ℂ v) = 0) → Λ = 0 := eq_zero_of_sepCont

end GlobalTheory.Core.Mi
