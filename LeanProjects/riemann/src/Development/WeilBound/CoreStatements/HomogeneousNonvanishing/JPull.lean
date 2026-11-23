import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem j_pull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k), IsBlockMap κ v → (∀ A : HermLine ι, ∃! A' : HermLine ι', IsPullHerm κ v A A') ∧ (∀ (A : HermLine ι) (A' : HermLine ι'), IsPullHerm κ v A A' → IsSmoothHerm A → IsSmoothHerm A') ∧ (∀ (P' : Ideal (MRing ι')), ∀ z ∈ mcPts P', (fun p => z (v p)) ∈ mcPts (imageZ v P')) ∧ ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
  intro K _ ι _ K' _ ι' _ κ v hv
  obtain ⟨hκ, hvi, hv1, hv2⟩ := hv
  have hnz : ∀ z : (Σ k, ι' k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ k, ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
    intro z hz k
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨⟨k', i⟩, hp⟩ := hv2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h1 : κ k' = κ k := by
      have := hv1 ⟨k', i⟩
      rw [hp] at this
      exact this.symm
    obtain rfl := hκ h1
    exact ⟨i, by rwa [hp]⟩
  have hev : ∀ (z : (Σ k, ι' k) → ℂ) (f : MRing ι), evC z (rename v f) = evC (fun p => z (v p)) f := by
    intro z f
    unfold evC
    rw [map_rename, eval_rename]
    rfl
  refine ⟨fun A => ⟨⟨pullDeg κ A.a, fun z => A.h fun p => z (v p), fun z hz => A.pos _ (hnz z hz), fun c z hc => ?_⟩,
    ⟨rfl, fun _ => rfl⟩, ?_⟩, fun A A' h hA => ?_, fun P' z hz => ⟨hnz z hz.1, fun f hf => ?_⟩, hev⟩
  · have h1 := A.smul (fun k => c (κ k)) (fun p => z (v p)) fun k => hc _
    simp only [hv1]
    rw [h1]
    congr 1
    refine Finset.prod_of_injOn κ hκ.injOn (fun _ _ => Finset.mem_univ _) (fun k' _ hk' => ?_) fun k _ => ?_
    · unfold pullDeg
      rw [Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · unfold pullDeg
      rw [hκ.extend_apply]
  · rintro ⟨a, h, _, _⟩ ⟨h1, h2⟩
    obtain rfl : a = pullDeg κ A.a := h1
    obtain rfl : h = fun z => A.h fun p => z (v p) := funext h2
    rfl
  · unfold IsSmoothHerm
    rw [show A'.h = A.h ∘ fun z p => z (v p) from funext h.2]
    exact ContDiffOn.comp hA (contDiffOn_pi.mpr fun p => (contDiff_apply ℝ ℂ (v p)).contDiffOn) fun z hz => hnz z hz
  · exact (hev z f).symm.trans (hz.2 _ hf)

end PositivityTheory.UnitarySelfGeneration
