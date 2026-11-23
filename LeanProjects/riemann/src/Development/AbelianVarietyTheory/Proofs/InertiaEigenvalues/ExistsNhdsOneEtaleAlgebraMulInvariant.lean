import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.MulInv

theorem exists_nhds_one_mul_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (φ : A.L → ℂ), IsTest φ →
    ∃ U ∈ 𝓝 (1 : A.K), ∀ s ∈ U, ∀ s' ∈ U, s * s' = 1 → ∀ y : A.L, φ (y * algebraMap A.K A.L s) = φ y := by
  intro F E _ _ _ _ _ A φ hφ
  obtain ⟨h1, h2⟩ := hφ
  let bil : A.K →ₗ[F] A.L →ₗ[F] A.L :=
    (LinearMap.mul F A.L).flip ∘ₗ (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hbil : Continuous fun p : A.K × A.L => bil p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left bil
  have hm : Continuous fun p : A.L × A.K => p.1 * algebraMap A.K A.L p.2 := by
    have := hbil.comp continuous_swap
    simpa [bil, Function.comp_def, mul_comm] using this
  have hl : IsLocallyConstant (fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) :=
    (h1.comp_continuous hm).prodMk (h1.comp_continuous continuous_fst)
  have ho : IsOpen ((fun p : A.L × A.K => (φ (p.1 * algebraMap A.K A.L p.2), φ p.1)) ⁻¹' {q | q.1 = q.2}) := hl _
  obtain ⟨u, v, -, hv, hu, h0, huv⟩ := generalized_tube_lemma (s := tsupport φ) (t := {(1 : A.K)}) h2
    isCompact_singleton ho (by rintro ⟨x, y⟩ ⟨-, hy⟩; simp at hy; simp [hy])
  refine ⟨v, hv.mem_nhds (h0 rfl), fun s hs s' hs' hss y => ?_⟩
  have key : ∀ x ∈ tsupport φ, ∀ t ∈ v, φ (x * algebraMap A.K A.L t) = φ x := fun x hx t ht =>
    huv (Set.mk_mem_prod (hu hx) ht)
  by_cases hy : y ∈ tsupport φ
  · exact key y hy s hs
  by_cases hy' : y * algebraMap A.K A.L s ∈ tsupport φ
  · have := key _ hy' s' hs'
    rw [mul_assoc, ← map_mul, hss, map_one, mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

end GlobalTheory.JR.MulInv
