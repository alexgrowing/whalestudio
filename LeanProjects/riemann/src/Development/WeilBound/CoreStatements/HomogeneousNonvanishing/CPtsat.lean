import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexConjugationHermCompatStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CMadens
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem ptsat_segre (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre]

theorem ptsat_cons (y : Fin e → ℂ) : star (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 (star y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem ptsat_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : star z ∈ mcPts P :=
  ((GlobalTheory.T.complex_conjugation_herm_compat K ι).1 P z).2 hz

theorem ptsat_symm (h : ∀ w, Ψ' w = star (Ψ (star w))) (w) : Ψ w = star (Ψ' (star w)) := by
  rw [h, star_star, star_star]

theorem ptsat_fibre (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w} (hw : w ∈ fibre P Ψ' y) :
    star w ∈ fibre P Ψ (star y) := by
  obtain ⟨z, hz, rfl, h2⟩ := hw
  exact ⟨star z, ptsat_mem hz, ptsat_segre z, by rw [ptsat_symm h, star_star, h2, ptsat_cons]⟩

theorem ptsat_sheet (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w γ} (hγ : IsSheet P Ψ' y w γ) :
    IsSheet P Ψ (star y) (star w) (star ∘ γ ∘ star) := by
  refine ⟨by simp only [Function.comp_apply, star_star, ptsat_segre, hγ.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star y)) (𝓝 y) := by
    simpa using (continuous_star (R := Fin e → ℂ)).tendsto (star y)
  filter_upwards [ht.eventually hγ.2] with y' hy'
  refine ⟨by simpa using hy'.1.star_star, ptsat_mem hy'.2.1, ?_⟩
  rw [ptsat_symm h, Function.comp_apply, Function.comp_apply, ptsat_segre, star_star, hy'.2.2, ptsat_cons,
    star_star]

end

theorem c_ptsat : SheetIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w i, Ψ' w i = starRingEnd ℂ (Ψ (fun c => starRingEnd ℂ (w c)) i)) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  intro hS K _ ι _ P e Ψ Ψ' L A s hP hΨ h0 hL hA hs
  have h : ∀ w, Ψ' w = star (Ψ (star w)) := fun w => funext (h0 w)
  refine ⟨fun z hz h1 => hΨ _ (ptsat_mem hz) (by rw [ptsat_symm h, ptsat_segre, star_star, h1, star_zero]), ?_⟩
  have hm : MeasureTheory.MeasurePreserving (star : (Fin e → ℂ) → Fin e → ℂ) :=
    MeasureTheory.volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have he : MeasurableEmbedding (star : (Fin e → ℂ) → Fin e → ℂ) :=
    (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
  unfold ptsIntegralAt
  rw [← hm.integral_comp he (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hm.quasiMeasurePreserving.ae (hS K ι P e Ψ L A s hP hΨ hL hA hs)] with y hy
  refine finsum_mem_eq_of_bijOn star ⟨fun w hw => ptsat_fibre h hw, star_injective.injOn, fun w hw =>
    ⟨star w, by simpa using ptsat_fibre (ptsat_symm h) hw, star_star w⟩⟩ fun w _ => ?_
  unfold sheetDensity
  by_cases h1 : ∃ γ, IsSheet P Ψ' y w γ
  · have h2 : ∃ γ, IsSheet P Ψ (star y) (star w) γ := ⟨_, ptsat_sheet h h1.choose_spec⟩
    rw [dif_pos h1, dif_pos h2, hy _ _ _ h2.choose_spec (ptsat_sheet h h1.choose_spec),
      (GlobalTheory.T.complex_conjugation_herm_compat K ι).2.2.2.1]
    have h3 := c_madens e (fun j y' => pot L j ((star ∘ h1.choose ∘ star) y')) y
    congr 1
    · simp only [Function.comp_apply, star_star]
      rfl
    · refine Eq.trans ?_ h3
      congr 1
      funext j y'
      show _ = pot L j (star (h1.choose (star (star y'))))
      rw [star_star]
      rfl
  · have h2 : ¬ ∃ γ, IsSheet P Ψ (star y) (star w) γ := fun ⟨γ, hγ⟩ =>
      h1 ⟨_, by simpa only [star_star] using ptsat_sheet (ptsat_symm h) hγ⟩
    rw [dif_neg h1, dif_neg h2]

end PositivityTheory.UnitarySelfGeneration
