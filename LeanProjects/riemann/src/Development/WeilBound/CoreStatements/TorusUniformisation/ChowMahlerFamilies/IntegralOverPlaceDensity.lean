import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.PlaceIntegralDensity

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sheetDensity_sum {S : Type} [Fintype S] {e : ℕ} (W : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (t : S → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : S → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity W Ψ ψ u y w = ∑ σ, t σ * sheetDensity W Ψ ψ (χ σ) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [h _ hγ.choose_spec.2.self_of_nhds.2.1, Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => by ring
  · simp

theorem finsum_mem_sum {α S : Type} [Fintype S] {s : Set α} (hs : s.Finite) (t : S → ℝ) (f : S → α → ℝ) :
    ∑ᶠ w ∈ s, ∑ σ, t σ * f σ w = ∑ σ, t σ * ∑ᶠ w ∈ s, f σ w := by
  simp only [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.mul_sum]
  exact Finset.sum_comm

theorem eq_sum {Ω : Type} [Field Ω] {F : Type} [Field F] [NumberField F] {y : (Σ k, ι k) → Ω} {φ : F →+* Ω}
    {t : (F →+* ℂ) → ℝ} {u : ((Σ k, ι k) → ℂ) → ℝ} {χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ}
    (hO : OverInt y φ) (hu : ∀ σ z, PtOver y φ σ z → u z = t σ)
    (hχ : ∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) : u z = ∑ σ, t σ * χ σ z := by
  obtain ⟨σ₀, hσ₀, -⟩ := existsUnique_ptOver _ _ _ _ y φ hO z hz
  rw [hu σ₀ z hσ₀, Finset.sum_eq_single σ₀]
  · rw [((hχ σ₀).near σ₀ z hσ₀).self_of_nhds]
    simp
  · intro b _ hb
    rw [((hχ b).near σ₀ z hσ₀).self_of_nhds]
    simp [Set.indicator, Ne.symm hb]
  · simp

end PositivityTheory.Xgn.PlaceIntegralDensity

open PositivityTheory.Xgn.PlaceIntegralDensity in
theorem PositivityTheory.Xgn.integral_over_place_density : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ) (χ : (F →+* ℂ) → ((Σ k, ι k) → ℂ) → ℝ), OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ z, PtOver y φ σ z → u z = t σ) → (∀ σ, IsPlaceWeight y φ (Set.indicator {σ} 1) (χ σ)) → ptsIntegral W (pot L) u = ∑ σ : F →+* ℂ, t σ * ptsIntegral W (pot L) (χ σ) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ W n L t u χ hO hW hA hL hu hχ
  have hmc : ∀ z ∈ mcPts W, z ∈ mcPts (mCoordIdeal y) := fun z hz => ⟨hz.1, fun f hf => hz.2 f (hW hf)⟩
  have hsum : ∀ z ∈ mcPts W, u z = ∑ σ, t σ * χ σ z := fun z hz => eq_sum hO hu hχ (hmc z hz)
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hfin := fibreFinite K ι W n hΨ.choose hA hΨ.choose_spec
    have hpt : ∀ y', ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), ∑ σ, t σ * sheetDensity W hΨ.choose (pot L) (χ σ) y' w =
        ∑ σ, t σ * ∑ᶠ (w) (_ : w ∈ fibre W hΨ.choose y'), sheetDensity W hΨ.choose (pot L) (χ σ) y' w :=
      fun y' => finsum_mem_sum (hfin y') t (fun σ w => sheetDensity W hΨ.choose (pot L) (χ σ) y' w)
    simp_rw [sheetDensity_sum W _ (pot L) t u χ hsum, hpt]
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_congr rfl fun σ _ => MeasureTheory.integral_const_mul (t σ) _
    · intro σ _
      refine MeasureTheory.Integrable.const_mul ?_ (t σ)
      let A : HermLine ι :=
        { a := fun _ => 0
          h := fun z => Real.exp (-χ σ z)
          pos := fun z _ => Real.exp_pos _
          smul := fun c z hc => by simp [(hχ σ).inv c z hc] }
      have hAs : IsSmoothHerm A := Real.contDiff_exp.comp_contDiffOn (hχ σ).smooth.neg
      have hsec : IsSectionOn W A 1 :=
        ⟨fun _ => 0, fun k => by simp [A], isMultiHomog_one,
          fun h => hA.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h)⟩
      have hlog : logNorm A 1 = χ σ := by
        funext z
        simp [logNorm, A, Real.exp_neg, Real.log_exp]
      have hI := hPI K ι W n hΨ.choose L A 1 hA hΨ.choose_spec hL hAs hsec
      rw [hlog] at hI
      exact hI
  · simp
