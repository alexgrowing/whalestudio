import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem AnPer.dw_comap_linear : ∀ {I I' : Type} [Fintype I] [Fintype I'] {g g' : ℕ} {W : Opens (Tot I g)} {W' : Opens (Tot I' g')} (b : (I' → ℂ) → I → ℂ) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ p ∈ W', AnalyticAt ℂ b p.1) → ∀ (hΦ : AnalyticOnNhd ℂ (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g)) W') (h : ∀ p ∈ W', ((b p.1, M p.2) : Tot I g) ∈ W) (a : Fin g') (f : Hol W), dw a (Hol.comap _ hΦ h f) = ∑ c, M (Pi.single a 1) c • Hol.comap _ hΦ h (dw c f) := by
  intro I I' _ _ g g' W W' b M hb hΦ h a f
  refine Hol.ext_fn fun p hp ↦ ?_
  have e : HasFDerivAt (fun p : Tot I' g' ↦ ((b p.1, M p.2) : Tot I g))
      (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _))) p :=
    ((hb p hp).differentiableAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk
      ((LinearMap.toContinuousLinearMap M).hasFDerivAt.comp p hasFDerivAt_snd)
  have hv : ((0 : I → ℂ), M (Pi.single a 1)) = ∑ c, M (Pi.single a 1) c • (((0 : I → ℂ), Pi.single c 1) : Tot I g) := by
    ext i
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  change (Hol.der _ (Hol.comap _ hΦ h f)).fn p = _
  rw [Hol.fn_der_comap _ _ _ _ f hp, e.fderiv]
  have e2 : (((fderiv ℂ b p.1).comp (ContinuousLinearMap.fst ℂ _ _)).prod
        ((LinearMap.toContinuousLinearMap M).comp (ContinuousLinearMap.snd ℂ _ _)))
        (((0 : I' → ℂ), Pi.single a 1) : Tot I' g') = ((0 : I → ℂ), M (Pi.single a 1)) := by
    simp
  rw [e2, hv, map_sum, ← Hol.ev_apply p hp, map_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Hol.ev_apply p hp, Hol.fn_comap _ _ _ _ hp]
  change _ = _ * (Hol.der _ f).fn _
  rw [Hol.fn_der _ _ (h p hp)]

end GlobalTheory
