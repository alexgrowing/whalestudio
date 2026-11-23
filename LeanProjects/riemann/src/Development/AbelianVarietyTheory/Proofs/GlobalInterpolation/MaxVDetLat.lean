import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.CharVal.DetFrame

theorem maxV_detLat (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n))
    (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) :
    MaxV P (detLat N) (P.valuation E ((LinearEquiv.det f : Eˣ) : E)) := by
  classical
  rw [LinearEquiv.coe_det]
  refine ⟨val_le_of_span ?_, ?_⟩
  · rintro a ⟨A, hA, rfl⟩
    let g : Sp E n →ₗ[E] Sp E n := Matrix.toLin' A
    have hg : ∀ x ∈ stdAt E n P, ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x ∈ stdAt E n P := by
      intro x hx
      rw [← hf]
      obtain ⟨s, hs, hx⟩ := (mem_locP P _ _).1 hx
      refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
      have h1 := hA _ hx
      have h2 : A.mulVec (s • x) = s • f (((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [Matrix.mulVec_smul]
        rfl
      rwa [h2] at h1
    have h := GlobalTheory.Survey.StandardDeterminantUnits.val_det_le_one _ hg
    have h3 : LinearMap.det (f : Sp E n →ₗ[E] Sp E n) *
        LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) = A.det := by
      rw [LinearMap.det_comp, ← mul_assoc, LinearEquiv.det_mul_det_symm, one_mul]
      exact LinearMap.det_toLin' A
    rw [← h3, map_mul]
    exact mul_le_of_le_one_right' h
  · have h1 : ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i (1 : E)) ∈ N := fun i =>
      (mem_locP P _ _).1 ((hf _).2 (le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)))
    choose s hs hs' using h1
    set t : 𝓞 E := ∏ i, s i with ht
    have htP : t ∉ P.asIdeal := by
      intro hm
      obtain ⟨i, -, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs i h
    have ht' : ∀ i, t • f (Pi.single i (1 : E)) ∈ N := by
      intro i
      rw [ht, ← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]
      exact N.smul_mem _ (hs' i)
    let g : Sp E n →ₗ[E] Sp E n := (algebraMap (𝓞 E) E t) • (f : Sp E n →ₗ[E] Sp E n)
    refine ⟨(LinearMap.toMatrix' g).det, Submodule.subset_span ⟨LinearMap.toMatrix' g, ?_, rfl⟩, ?_⟩
    · intro v hv
      have h2 : (LinearMap.toMatrix' g).mulVec v = t • f v := by
        rw [LinearMap.toMatrix'_mulVec]
        simp [g]
      rw [h2]
      clear h2
      rw [stdLat_eq_span] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ht' i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, smul_add]; exact N.add_mem hx hy
      | smul r x _ hx =>
        rw [← algebraMap_smul E r x, map_smul, algebraMap_smul, smul_comm]
        exact N.smul_mem r hx
    · rw [LinearMap.det_toMatrix', LinearMap.det_smul, map_mul, map_pow,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 htP, one_pow, one_mul]

end GlobalTheory.CharVal.DetFrame
