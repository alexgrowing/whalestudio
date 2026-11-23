import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨θ, hθ⟩ := exists_theta_vec D m
  obtain ⟨ζ, hζZ, -, hζs, hopp⟩ := h.exists_rank_one hm θ hθ
  have himg' : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg'' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ (Z'.subtype + ℓ.smulRight (m + ζ ℓ)) = y ∘ₗ Z'.subtype + ℓ.smulRight (y (m + ζ ℓ)) := by
      ext x; simp
    rw [img, ← LinearMap.range_comp, this]
  have he𝔭 : e ∉ 𝔭 := fun h' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' he1))
  have hℓv : (e • ℓ₀) v ∉ 𝔭 := by
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact fun h' => (h𝔭.isPrime.mem_or_mem h').elim he𝔭 hℓ₀
  have hker := range_le_of_ker (y ∘ₗ Z'.subtype) (e • ℓ₀) (y (m + ζ (e • ℓ₀))) 𝔭 h𝔭 (v := v) hv hℓv
  refine ⟨_, hopp (e • ℓ₀), fun 𝔮 h𝔮 hn𝔮 => ?_, ?_⟩
  · rw [himg', himg'']
    by_cases hq : 𝔮 = 𝔭
    · subst hq; exact hker.2
    · exact range_le_of_mem _ _ _ 𝔮 fun x => by
        rw [LinearMap.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · rw [himg'']
    intro hle
    have hu' := hle hker.1
    have hz : y (ζ (e • ℓ₀)) ∈ img D y Z' 𝔭 := by
      rcases hA with hA | hA
      · haveI := h𝔭
        have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
        have hn' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
          simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
        have he' := he _ h𝔭' hn' hA
        rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at he'
        have hbe : H.bar e ∈ 𝔭 := by
          have : H.bar.symm e = H.bar e := by rw [RingEquiv.symm_apply_eq, bar_bar]
          rwa [this] at he'
        rw [hζs, map_smul]
        exact Submodule.mem_sup_right (Submodule.smul_mem_smul hbe trivial)
      · exact hA (Submodule.mem_map_of_mem (hζZ _))
    apply hym
    have : y m = y (m + ζ (e • ℓ₀)) - y (ζ (e • ℓ₀)) := by simp
    rw [this]
    exact sub_mem hu' hz

end GlobalTheory.LowFilt
