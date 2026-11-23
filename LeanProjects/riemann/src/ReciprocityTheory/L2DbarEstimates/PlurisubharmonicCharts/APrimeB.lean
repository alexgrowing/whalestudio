import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

theorem aprb_complement {n d : ℕ} (Lm : V n →L[ℂ] V d) (hs : Function.Surjective Lm) :
    ∃ A : V n ≃L[ℂ] V d × V (n - d), ∀ v, (A v).1 = Lm v := by
  classical
  let K := LinearMap.ker (Lm : V n →ₗ[ℂ] V d)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  let P : V n →ₗ[ℂ] K := Submodule.linearProjOfIsCompl K C hC
  have hrank : Module.finrank ℂ (V d) + Module.finrank ℂ K = Module.finrank ℂ (V n) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Lm : V n →ₗ[ℂ] V d)
    rwa [LinearMap.range_eq_top.mpr hs, finrank_top] at h1
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hrank
  have hK : Module.finrank ℂ K = n - d := by omega
  let eK : K ≃ₗ[ℂ] V (n - d) := LinearEquiv.ofFinrankEq K (V (n - d)) (by rw [hK]; simp)
  let T : V n →ₗ[ℂ] V d × V (n - d) := LinearMap.prod (Lm : V n →ₗ[ℂ] V d) (eK.toLinearMap ∘ₗ P)
  have hT : Function.Injective T := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
    have h1 : Lm v = 0 := by simpa [T] using congrArg Prod.fst hv
    have h2 : P v = 0 := by simpa [T] using congrArg Prod.snd hv
    have hvK : v ∈ K := by simpa [K] using h1
    have h3 := Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hvK⟩
    have h4 : (⟨v, hvK⟩ : K) = 0 := h3.symm.trans h2
    simpa using congrArg Subtype.val h4
  have hdim : Module.finrank ℂ (V n) = Module.finrank ℂ (V d × V (n - d)) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine ⟨(LinearMap.linearEquivOfInjective T hT hdim).toContinuousLinearEquiv, fun v => ?_⟩
  rfl

theorem aprb_contDiffOn {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) (k : ℕ) : ContDiffOn ℂ k p U := by
  rw [contDiffOn_euclidean]
  intro i
  have h1 : DifferentiableOn ℂ (fun x => p x i) U :=
    (EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp
  exact (contDiffOn_of_differentiableOn n _ U hU h1).of_le (by exact_mod_cast le_top)

end

end ReciprocityTheory.L2DbarEstimates.Y
