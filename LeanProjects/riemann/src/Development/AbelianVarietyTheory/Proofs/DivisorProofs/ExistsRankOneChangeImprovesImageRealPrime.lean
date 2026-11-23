import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGeneratorStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem mem_of_smul_mem_sup {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O} (hI : I.IsMaximal)
    {N : Submodule O X} (hN : I • (⊤ : Submodule O X) ≤ N) {a : O} (ha : a ∉ I) {u : X} (hu : a • u ∈ N) : u ∈ N := by
  obtain ⟨c, i, hi, hc⟩ := hI.exists_inv ha
  have : c • (a • u) + i • u = u := by rw [smul_smul, ← add_smul, hc, one_smul]
  rw [← this]
  exact add_mem (N.smul_mem c hu) (hN (Submodule.smul_mem_smul hi trivial))

theorem map_range_rank_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (Z' : Submodule (𝓞 E) D.La)
    (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (u : D.La) :
    (LinearMap.range (Z'.subtype + ℓ.smulRight u)).map y = LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y u)) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext x
  simp

end GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_real {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  have hm : (0 : D.La) ∈ perp D Z ⊓ perp D Z' := zero_mem _
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one hm θ (fun t => by simp [hθ])
  have hN : 𝔭 • (⊤ : Submodule (𝓞 E) X) ≤ img D y Z' 𝔭 := le_sup_right

  set P1 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => ℓ v ∈ 𝔭 with hP1
  set P2 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭 with hP2
  have P1sub : ∀ a b, P1 (a + b) → P1 b → P1 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP1] using this
  have P2sub : ∀ a b, P2 (a + b) → P2 b → P2 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP2, map_add] using this

  obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := Set.not_subset.1 hZ
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔭.zero_mem)
  obtain ⟨ℓ₂, hℓ₂⟩ := GlobalTheory.T.exists_linearForm_factor_through_traceGenerator D Z' θ s hs0 hgen z
  have hζ₂ : ζ ℓ₂ = H.bar s • z := by
    obtain ⟨c, -, hu⟩ := h.symm.2.2.1 (θ.comp ℓ₂.toAddMonoidHom)
    have e1 := hu ⟨ζ ℓ₂, hζZ ℓ₂⟩ fun a => by simpa using hζ ℓ₂ a
    have e2 := hu ⟨H.bar s • z, Z.smul_mem _ hz⟩ fun a => by simpa using (hℓ₂ a).symm
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hℓ₂P : ¬ P2 ℓ₂ := fun hP => by
    simp only [hP2, hζ₂, map_smul] at hP
    exact hx (mem_of_smul_mem_sup h𝔭 hN hs' hP)

  obtain ⟨ℓ₁, h1, h2⟩ : ∃ ℓ₁, ¬ P1 ℓ₁ ∧ ¬ P2 ℓ₁ := by
    by_cases ha : P2 ℓ₀
    · by_cases hb1 : P1 ℓ₂
      · refine ⟨ℓ₀ + ℓ₂, fun hp => hℓ₀ (P1sub _ _ hp hb1), fun hp => hℓ₂P ?_⟩
        rw [add_comm] at hp
        exact P2sub _ _ hp ha
      · exact ⟨ℓ₂, hb1, hℓ₂P⟩
    · exact ⟨ℓ₀, hℓ₀, ha⟩
  have he𝔭 : e ∉ 𝔭 := fun hm' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem hm' he1
    simpa using this))
  have hbe : H.bar e ∉ 𝔭 := fun hm' => he𝔭 (by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm'
    rw [hb] at this
    simpa [bar_bar] using this)
  set ℓ := e • ℓ₁ with hℓ
  refine ⟨LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)), hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => ?_⟩
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    show Z'.map y ⊔ _ ≤ _ ⊔ _
    rw [map_range_rank_one, hZ'm]
    by_cases hq : 𝔮 = 𝔭
    · subst hq
      refine (range_le_of_ker _ ℓ _ 𝔮 h𝔮 (v := v) (by simpa using hv) ?_).2
      show e * ℓ₁ v ∉ 𝔮
      exact fun hm' => h1 ((h𝔮.isPrime.mem_or_mem hm').resolve_left he𝔭)
    · exact range_le_of_mem _ ℓ _ 𝔮 fun x => by
        show e * ℓ₁ x ∈ 𝔮
        exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmem := (range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (0 + ζ ℓ)) 𝔭 h𝔭 (v := v) (by simpa using hv)
      (show e * ℓ₁ v ∉ 𝔭 from fun hm' => h1 ((h𝔭.isPrime.mem_or_mem hm').resolve_left he𝔭))).1
    have hin : y (ζ ℓ) ∈ img D y Z' 𝔭 := by
      apply hle
      show _ ∈ _ ⊔ _
      rw [map_range_rank_one]
      simpa using hmem
    rw [hℓ, hζs, map_smul] at hin
    exact h2 (mem_of_smul_mem_sup h𝔭 hN hbe hin)

end GlobalTheory.LowFilt
