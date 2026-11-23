import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOfQuot

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig :
    ∀ {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (y : Y), y ≠ 0 → (∀ i, A i y = x i • y) → ∃ φ : Module.Dual K Y, φ ≠ 0 ∧ ∀ i z, φ (A i z) = x i * φ z := by
  intro K Y ι _ _ _ _ A hA x y hy hAy
  have hc : ∀ i j, Commute (A i).dualMap (A j).dualMap := by
    intro i j
    show (A i).dualMap * (A j).dualMap = (A j).dualMap * (A i).dualMap
    refine LinearMap.ext fun ψ => LinearMap.ext fun z => ?_
    have h := LinearMap.congr_fun (hA j i).eq z
    simp only [Module.End.mul_apply] at h
    simp only [Module.End.mul_apply, LinearMap.dualMap_apply]
    rw [h]
  have hne : Module.Dual.eval K Y y ≠ 0 := by
    intro h0
    apply hy
    refine (Module.forall_dual_apply_eq_zero_iff K y).mp ?_
    intro ψ
    exact LinearMap.congr_fun h0 ψ
  obtain ⟨ψ, hψ, hψA⟩ := eigOfQuot (fun i => (A i).dualMap) hc x (Module.Dual.eval K Y y) hne (by
    intro i ψ
    simp [LinearMap.dualMap_apply, hAy])
  refine ⟨ψ, hψ, fun i z => ?_⟩
  have := LinearMap.congr_fun (hψA i) z
  simpa [LinearMap.dualMap_apply] using this
