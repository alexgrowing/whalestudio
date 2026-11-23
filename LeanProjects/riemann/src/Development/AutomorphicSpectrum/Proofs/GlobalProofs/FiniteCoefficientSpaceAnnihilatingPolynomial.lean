import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HcFinite.OneParam

theorem hasDerivAt_of_oneParam {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] (φ : ℝ → E)
    (hc : Continuous φ) (h0 : φ 0 = 1) (hadd : ∀ a b, φ (a + b) = φ a * φ b) :
    ∃ D : E, ∀ t, HasDerivAt φ (φ t * D) t := by
  set I : ℝ → E := fun u => ∫ x in (0:ℝ)..u, φ x with hI
  have hId : ∀ b, HasDerivAt I (φ b) b := fun b => (hc.integral_hasStrictDerivAt 0 b).hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hId 0)
  rw [h0] at hslope
  have hev : ∀ᶠ r in 𝓝[≠] (0:ℝ), ‖slope I 0 r - 1‖ < 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hslope).eventually (gt_mem_nhds one_pos)
  obtain ⟨r, hr, hne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hlt : ‖1 - slope I 0 r‖ < 1 := by rw [norm_sub_rev]; exact hr
  obtain ⟨u, hu⟩ : IsUnit (slope I 0 r) := by
    have e : slope I 0 r = 1 - (1 - slope I 0 r) := by abel
    rw [e]
    exact ⟨Units.oneSub (1 - slope I 0 r) hlt, rfl⟩
  have key : ∀ t, φ t * I r = I (t + r) - I t := by
    intro t
    have h1 : φ t * I r = ∫ x in (0:ℝ)..r, φ (t + x) := by
      have hcomm := (ContinuousLinearMap.mul ℝ E (φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 r)
      simp only [ContinuousLinearMap.mul_apply'] at hcomm
      rw [hI, ← hcomm]
      simp only [hadd]
    rw [h1, intervalIntegral.integral_comp_add_left (fun x => φ x) t, add_zero, hI,
      intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have hI0 : I 0 = 0 := by simp [hI]
  have hφ : φ = fun t => (r⁻¹ • (I (t + r) - I t)) * ((u⁻¹ : Eˣ) : E) := by
    funext t
    have e : φ t * slope I 0 r = r⁻¹ • (I (t + r) - I t) := by
      rw [slope_def_module, sub_zero, hI0, sub_zero, mul_smul_comm, key]
    rw [← e, ← hu, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨r⁻¹ • (φ r - 1) * ((u⁻¹ : Eˣ) : E), fun t => ?_⟩
  have h2 : HasDerivAt (fun t => I (t + r)) (φ (t + r)) t := HasDerivAt.comp_add_const t r (hId (t + r))
  have hd : HasDerivAt (fun t => (r⁻¹ • (I (t + r) - I t)) * ((u⁻¹ : Eˣ) : E))
      ((r⁻¹ • (φ (t + r) - φ t)) * ((u⁻¹ : Eˣ) : E)) t :=
    ((h2.sub (hId t)).const_smul r⁻¹).mul_const _
  rw [← hφ] at hd
  convert hd using 1
  rw [hadd, ← mul_assoc, mul_smul_comm, mul_sub, mul_one]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exists_generator {K W : Type} [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ K W) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) (s : ℝ → K)
    (hs : Continuous s) (h0 : s 0 = 1) (hadd : ∀ a b, s (a + b) = s a * s b) :
    ∃ D : Module.End ℂ W, ∀ (L : Module.End ℂ W →ₗ[ℂ] ℂ) (t : ℝ),
      HasDerivAt (fun t => L (ρ (s t))) (L (ρ (s t) * D)) t := by
  let b := Module.finBasis ℂ W
  let M : ℝ → Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun t => LinearMap.toMatrix b b (ρ (s t))
  have hM0 : M 0 = 1 := by simp [M, h0]
  have hMadd : ∀ a c, M (a + c) = M a * M c := by
    intro a c
    simp only [M, hadd, map_mul, LinearMap.toMatrix_mul]
  have hMc : Continuous M := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [M, LinearMap.toMatrix_apply]
    exact (hρ (b.coord i) (b j)).comp hs
  obtain ⟨D₀, hD₀⟩ := hasDerivAt_of_oneParam M hMc hM0 hMadd
  refine ⟨Matrix.toLin b b D₀, fun L t => ?_⟩
  let L' : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap ((L ∘ₗ (Matrix.toLin b b).toLinearMap).restrictScalars ℝ)
  have hL' : ∀ X, L' X = L (Matrix.toLin b b X) := fun X => rfl
  have hk := L'.hasFDerivAt.comp_hasDerivAt t (hD₀ t)
  have e1 : (fun t => L (ρ (s t))) = L' ∘ M := by
    funext t
    simp [hL', M, Matrix.toLin_toMatrix]
  rw [e1]
  convert hk using 1
  show L (ρ (s t) * Matrix.toLin b b D₀) = L (Matrix.toLin b b (LinearMap.toMatrix b b (ρ (s t)) * D₀))
  rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, Module.End.mul_eq_comp]
  all_goals rfl

theorem iteratedDeriv_eq {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (s : ℝ → K)
    (D : Module.End ℂ W)
    (hD : ∀ (L : Module.End ℂ W →ₗ[ℂ] ℂ) (t : ℝ), HasDerivAt (fun t => L (ρ (s t))) (L (ρ (s t) * D)) t) (j : ℕ) :
    ∀ L : Module.End ℂ W →ₗ[ℂ] ℂ, iteratedDeriv j (fun t => L (ρ (s t))) = fun t => L (ρ (s t) * D ^ j) := by
  induction j with
  | zero =>
    intro L
    funext t
    simp
  | succ j ih =>
    intro L
    rw [iteratedDeriv_succ, ih L]
    funext t
    have h := hD (L ∘ₗ LinearMap.mulRight ℂ (D ^ j)) t
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at h
    rw [h.deriv, mul_assoc, ← pow_succ']

theorem coeffSpan_factor {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W)
    (f : K → ℂ) (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) :
    ∃ Λ : Module.End ℂ W →ₗ[ℂ] ℂ, ∀ x, f x = Λ (ρ x) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ℓ, w, rfl⟩ := hg
    exact ⟨ℓ ∘ₗ (LinearMap.applyₗ w : Module.End ℂ W →ₗ[ℂ] W), fun x => rfl⟩
  | zero => exact ⟨0, fun x => by simp⟩
  | add g h _ _ hg hh =>
    obtain ⟨Λ₁, h₁⟩ := hg
    obtain ⟨Λ₂, h₂⟩ := hh
    exact ⟨Λ₁ + Λ₂, fun x => by simp [h₁, h₂]⟩
  | smul c g _ hg =>
    obtain ⟨Λ, hΛ⟩ := hg
    exact ⟨c • Λ, fun x => by simp [hΛ]⟩

theorem coeff_ode : ∀ (K W : Type) [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ s : ℝ → K, Continuous s → s 0 = 1 → (∀ a b, s (a + b) = s a * s b) → ∃ m : Polynomial ℂ, m ≠ 0 ∧ ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k : K, ∑ j ∈ Finset.range (m.natDegree + 1), m.coeff j * iteratedDeriv j (fun t : ℝ => f (k * s t)) 0 = 0 := by
  intro K W _ _ _ _ _ ρ hρ s hs h0 hadd
  obtain ⟨D, hD⟩ := exists_generator ρ hρ s hs h0 hadd
  refine ⟨LinearMap.charpoly D, (LinearMap.charpoly_monic D).ne_zero, ?_⟩
  intro f hf k
  obtain ⟨Λ, hΛ⟩ := coeffSpan_factor ρ f hf
  let L : Module.End ℂ W →ₗ[ℂ] ℂ := Λ ∘ₗ LinearMap.mulLeft ℂ (ρ k)
  have hfun : (fun t : ℝ => f (k * s t)) = fun t => L (ρ (s t)) := by
    funext t
    simp [L, hΛ, map_mul]
  have hit := iteratedDeriv_eq ρ s D hD
  simp only [hfun, hit]
  simp only [h0, map_one, one_mul]
  have hc := LinearMap.aeval_self_charpoly D
  rw [Polynomial.aeval_eq_sum_range] at hc
  calc ∑ j ∈ Finset.range ((LinearMap.charpoly D).natDegree + 1), (LinearMap.charpoly D).coeff j * L (D ^ j)
      = L (∑ j ∈ Finset.range ((LinearMap.charpoly D).natDegree + 1), (LinearMap.charpoly D).coeff j • D ^ j) := by
        simp [map_sum, smul_eq_mul]
    _ = 0 := by rw [hc, map_zero]

end GlobalTheory.CompanionTheory.HcFinite.OneParam
