import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem Lat.wedge_eq_span_of_isFrameAt :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E]
      [Module Ω E] (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p : Cpt ξ), L.IsFrameAt b p →
      L.wedge r p = Submodule.span (regAt ξ p) {exteriorPower.ιMulti Ω r b} := by
  intro X Ω _ ξ E _ _ L r b p h
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨v, hv, rfl⟩
    have hc : ∀ i, ∃ c : Fin r → regAt ξ p, ∑ j, c j • b j = v i := fun i => by
      have := hv i
      rw [h.2] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using hc
    have hv' : v = fun i => ∑ j, ((c i j : Ω)) • b j := by
      funext i
      rw [← hc i]
      rfl
    have hsum : exteriorPower.ιMulti Ω r v =
        ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
      rw [hv']
      have := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
        (fun i j => ((c i j : Ω)) • b j)
      refine this.trans (Finset.sum_congr rfl fun f _ => ?_)
      have h2 := (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
        (fun i => (c i (f i) : Ω)) (fun i => b (f i))
      refine h2.trans ?_
      have h3 : ((∏ i, c i (f i) : regAt ξ p) : Ω) = ∏ i, (c i (f i) : Ω) := by simp
      rw [← h3]
      rfl
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h4 := (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, h4]
      have hm := Submodule.mem_span_singleton_self (R := regAt ξ p) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  · refine Submodule.span_mono ?_
    rintro w rfl
    refine ⟨b, fun i => ?_, rfl⟩
    rw [h.2]
    exact Submodule.subset_span ⟨i, rfl⟩

end GlobalTheory.CompanionTheory.Ar
