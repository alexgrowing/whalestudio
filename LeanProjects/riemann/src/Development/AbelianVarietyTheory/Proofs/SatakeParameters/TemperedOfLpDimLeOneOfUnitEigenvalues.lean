import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem absSpace_eq_bot_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) {r : ℝ} (hr : r ≠ 1) :
    absSpace f r = ⊥ := by
  refine eq_bot_iff.mpr (iSup₂_le fun α hα => ?_)
  by_contra hne
  have hev : f.HasEigenvalue α := Module.End.hasEigenvalue_iff.mpr fun h => hne (h ▸ le_refl _)
  have hroot : (minpoly ℂ f).IsRoot α := Module.End.hasEigenvalue_iff_isRoot.mp hev
  have hc : α ∈ f.charpoly.roots := by
    rw [mem_roots (LinearMap.charpoly_monic f).ne_zero, ← Polynomial.dvd_iff_isRoot]
    exact (Polynomial.dvd_iff_isRoot.mpr hroot).trans (LinearMap.minpoly_dvd_charpoly f)
  exact hr (hα ▸ hf α hc)

theorem absSpace_one_eq_top_of_norm_charpoly_roots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hs : f.IsSemisimple) (hf : ∀ α ∈ f.charpoly.roots, ‖α‖ = 1) :
    absSpace f 1 = ⊤ := by
  rw [eq_top_iff, ← hs.iSup_eigenspace_eq_top]
  refine iSup_le fun α => ?_
  by_cases hα : ‖α‖ = 1
  · exact le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = 1) => f.eigenspace β) α hα le_rfl
  · have := absSpace_eq_bot_of_norm_charpoly_roots hf hα
    rw [eq_bot_iff] at this
    refine le_trans ?_ (bot_le : (⊥ : Submodule ℂ V) ≤ absSpace f 1)
    exact le_trans (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = ‖α‖) => f.eigenspace β) α rfl le_rfl) this

end GlobalTheory.WeilDeligne

theorem GlobalTheory.WeilDeligne.WD.tempered_of_lpDim_le_one_of_norm_eig : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : WD h), a.lpDim ≤ 1 → (∀ φ : Weil h, deg φ = 1 → ∀ α ∈ a.eig φ, ‖α‖ = 1) → a.tempered := by
  intro E Ω _ _ _ _ _ A w h a _ heig
  induction a using WD.ind with
  | hP n a =>
  rw [WD.tempered_mk]
  intro φ hφ
  have hroots : ∀ α ∈ (a.ρ φ).charpoly.roots, ‖α‖ = 1 := by
    intro α hα; exact heig φ hφ α (by rw [WD.eig_mk]; exact hα)
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hne : ∀ s : ℝ, s ≠ 0 → ((normV w : ℕ) : ℝ) ^ s ≠ 1 := by
    intro s hs h1
    rw [← Real.rpow_zero ((normV w : ℕ) : ℝ), Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at h1
    exact hs h1
  refine ⟨eq_top_iff.mpr ?_, fun i => ?_⟩
  · rw [← absSpace_one_eq_top_of_norm_charpoly_roots (a.semisimple φ) hroots]
    refine le_iSup_of_le (0 : ℤ) ?_
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [pow_zero, Nat.cast_zero, neg_zero]
      exact Set.bijOn_id _
    · have hi' : (0 : ℝ) < i := by exact_mod_cast hi
      rw [absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith)),
        absSpace_eq_bot_of_norm_charpoly_roots hroots (hne _ (by linarith))]
      simp only [Submodule.bot_coe]
      exact ⟨fun v hv => by rw [Set.mem_singleton_iff.mp hv, map_zero]; rfl,
        fun v hv v' hv' _ => by rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp hv'],
        fun v hv => ⟨0, rfl, by rw [Set.mem_singleton_iff.mp hv, map_zero]⟩⟩
