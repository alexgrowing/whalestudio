import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerCoordExists

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj colMat)

namespace UpperTheory.Gal.W2

theorem perCoordLoc_of : PerCoordLoc := by
  intro O _ bar g ρ D P₀ M₀ hP₀ hM₀ d co hco m B P b₀ hB hb₀ hHol hPb₀
  obtain ⟨α, β, hαβ⟩ := PerCoordU.exists_colMat_per hP₀
  obtain ⟨A, hA⟩ : ∃ A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, A b = colMat α ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, Bm b = colMat β ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  have hrep : ∀ b ∈ B, ∀ x, P b x = realMap (A b) (Bm b) (P₀ x) := by
    intro b hb x
    rw [hA, hBm]
    exact hαβ _ (hHol.1 b hb) x
  have hPd : ∀ (x : D.La) (i : Fin g), DifferentiableOn ℂ (fun b => P b x i) B :=
    fun x i => differentiableOn_pi.1 (hHol.2 x) i
  have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := by
    intro i j
    simp only [hA, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hBd : ∀ i j, DifferentiableOn ℂ (fun b => Bm b i j) B := by
    intro i j
    simp only [hBm, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hAc : ContinuousOn A B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hdet : ContinuousOn (fun b => (A b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hAc
  have hSo : IsOpen (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton
  have hAB0 : A b₀ = 1 ∧ Bm b₀ = 0 := by
    apply realMap_inj
    apply PerCoordU.ext_per hP₀
    intro x
    have h1 := hrep b₀ hb₀ x
    rw [hPb₀] at h1
    rw [← h1, realMap_apply]
    simp
  have hb₀S : b₀ ∈ B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ := by
    refine ⟨hb₀, ?_⟩
    simp [hAB0.1]
  have hnhds : B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ ∈ 𝓝 b₀ := hSo.mem_nhds hb₀S
  have hinvd : ∀ i j, DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹)
      (fun i j => (hAd i j).mono Set.inter_subset_left)
      (fun b hb => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by simpa using hb.2)))
  obtain ⟨gL, hgL⟩ := LinearMap.exists_leftInverse_of_injective co (LinearMap.ker_eq_bot.mpr hco.1)
  refine ⟨fun b => gL ((A b)⁻¹ * Bm b), ?_, ?_, ?_⟩
  · rw [differentiableAt_pi]
    intro k
    have e : (fun b => gL ((A b)⁻¹ * Bm b) k) =
        fun b => ∑ i, ∑ j, ((A b)⁻¹ * Bm b) i j * gL (Matrix.single i j 1) k :=
      funext fun b => PerCoordU.coords_sum gL _ k
    rw [e]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.mul_const ?_ _
    simp only [Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_mul ?_ ?_
    · exact (hinvd i l).differentiableAt hnhds
    · exact (hBd l j).differentiableAt (hB.mem_nhds hb₀)
  · simp only
    rw [hAB0.1, hAB0.2, Matrix.mul_zero, map_zero]
  · filter_upwards [hnhds] with b hb
    have hdetb : IsUnit (A b).det := isUnit_iff_ne_zero.mpr (by simpa using hb.2)
    have hCmem : (A b)⁻¹ * Bm b ∈ LinearMap.range co := by
      rw [hco.2]
      exact PerCoordU.mem_Tsp_of_period hP₀ (hHol.1 b hb.1) hM₀.2.2 (hrep b hb.1) hdetb.ne_zero
    obtain ⟨y, hy⟩ := hCmem
    have hcy : co (gL ((A b)⁻¹ * Bm b)) = (A b)⁻¹ * Bm b := by
      rw [← hy, ← LinearMap.comp_apply gL co, hgL, LinearMap.id_apply]
    letI := Matrix.invertibleOfIsUnitDet (A b) hdetb
    refine ⟨Matrix.toLinearEquiv' (A b) this, fun x => ?_⟩
    simp only [hcy, perC_apply]
    rw [hrep b hb.1 x, realMap_apply]
    show A b *ᵥ P₀ x + Bm b *ᵥ star (P₀ x) = A b *ᵥ (P₀ x + ((A b)⁻¹ * Bm b) *ᵥ star (P₀ x))
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdetb]

end UpperTheory.Gal.W2
