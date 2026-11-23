import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGenerator

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_not_and_not_of_sub_closed {A : Type} [AddCommGroup A] (P Q : A → Prop)
    (hP : ∀ a b, P a → P b → P (a - b)) (hQ : ∀ a b, Q a → Q b → Q (a - b)) {a b : A} (ha : ¬ P a) (hb : ¬ Q b) :
    ∃ c, ¬ P c ∧ ¬ Q c := by
  by_cases h1 : Q a
  · by_cases h2 : P b
    · refine ⟨a + b, fun h => ha ?_, fun h => hb ?_⟩
      · simpa using hP _ _ h h2
      · simpa using hQ _ _ h h1
    · exact ⟨b, h2, hb⟩
  · exact ⟨a, ha, h1⟩

theorem mem_map_bar_iff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E)) (x : 𝓞 E) :
    x ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ↔ H.bar x ∈ 𝔭 := by
  rw [Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) (fun a => ⟨H.bar a, bar_bar H a⟩)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have := bar_bar H a
    simpa [this] using ha
  · exact fun hx => ⟨_, hx, bar_bar H x⟩

theorem mem_of_smul_mem_of_not_mem {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O}
    (hI : I.IsMaximal) (N : Submodule O X) {c : O} (hc : c ∉ I) {x : X} (hx : c • x ∈ N ⊔ I • (⊤ : Submodule O X)) :
    x ∈ N ⊔ I • (⊤ : Submodule O X) := by
  obtain ⟨d, i, hi, hd⟩ := hI.exists_inv hc
  have : x = d • (c • x) + i • x := by rw [smul_smul, ← add_smul, hd, one_smul]
  rw [this]
  exact add_mem (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))

theorem exists_improves_of_ne_conj : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  intro E _ _ _ H D X _ _ y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ
  set 𝔭' := 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) with h𝔭'def
  have hmem : ∀ x, x ∈ 𝔭' ↔ H.bar x ∈ 𝔭 := mem_map_bar_iff H 𝔭
  have h𝔭' : 𝔭'.IsMaximal := by
    have : 𝔭' = 𝔭.comap (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.ext fun x => hmem x
    rw [this]
    exact Ideal.comap_isMaximal_of_surjective _ (fun a => ⟨H.bar a, bar_bar H a⟩)
  have hn' : (n : 𝓞 E) ∈ 𝔭' := (hmem _).2 (by simpa using hn𝔭)
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one (m := 0) (zero_mem _) θ (fun t => by simp [hθ])
  have himg : ∀ I : Ideal (𝓞 E), img D y Z' I = LinearMap.range (y ∘ₗ Z'.subtype) ⊔ I • ⊤ := fun I => by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have himg' : ∀ (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (I : Ideal (𝓞 E)),
      img D y (LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ))) I =
        LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ))) ⊔ I • ⊤ := fun ℓ I => by
    have : y ∘ₗ Z'.subtype + ℓ.smulRight (y (ζ ℓ)) = y ∘ₗ (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)) := by
      ext x; simp
    rw [this, LinearMap.range_comp]

  obtain ⟨ℓ₂, hℓ₂⟩ : ∃ ℓ₂, y (ζ ℓ₂) ∉ img D y Z' 𝔭 := by
    obtain ⟨_, ⟨z, hz, rfl⟩, hz'⟩ := SetLike.not_le_iff_exists.1 hZ
    obtain ⟨ℓ, hℓ⟩ := GlobalTheory.LowFilt.exists_linear_theta_factor D Z' θ s (fun h0 => hs (h0 ▸ zero_mem _)) hgen z
    have h0 : ζ ℓ - H.bar s • z = 0 := h.symm.eq_zero (sub_mem (hζZ ℓ) (Z.smul_mem _ hz)) fun x hx => by
      rw [ef_swap, map_sub, hζ ℓ ⟨x, hx⟩, hℓ ⟨x, hx⟩]; simp
    refine ⟨ℓ, fun hh => hz' ?_⟩
    rw [sub_eq_zero.1 h0, map_smul] at hh
    exact mem_of_smul_mem_of_not_mem h𝔭 _ hs' hh
  obtain ⟨ℓ', h1, h2⟩ := exists_not_and_not_of_sub_closed (fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => ℓ v₂ ∈ 𝔭')
    (fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭) (fun a b ha hb => sub_mem ha hb)
    (fun a b ha hb => by simpa only [map_sub] using sub_mem ha hb) hℓ₁ hℓ₂
  have he𝔭' : e ∈ 𝔭' := he _ h𝔭' hn' hb
  have he'𝔭 : e' ∈ 𝔭 := he' _ h𝔭 hn𝔭 hb.symm
  set ℓ := e • ℓ₀ + e' • ℓ' with hℓdef
  have hℓx : ∀ x, ℓ x = e * ℓ₀ x + e' * ℓ' x := fun x => rfl
  have hv𝔭 : ℓ v ∉ 𝔭 := fun hh => hℓ₀ (by
    have : ℓ₀ v = ℓ v - (e - 1) * ℓ₀ v - e' * ℓ' v := by rw [hℓx]; ring
    rw [this]
    exact sub_mem (sub_mem hh (𝔭.mul_mem_right _ he1)) (𝔭.mul_mem_right _ he'𝔭))
  have hv𝔭' : ℓ v₂ ∉ 𝔭' := fun hh => h1 (by
    have : ℓ' v₂ = ℓ v₂ - (e' - 1) * ℓ' v₂ - e * ℓ₀ v₂ := by rw [hℓx]; ring
    show ℓ' v₂ ∈ 𝔭'
    rw [this]
    exact sub_mem (sub_mem hh (𝔭'.mul_mem_right _ he1')) (𝔭'.mul_mem_right _ he𝔭'))
  have k𝔭 := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭 h𝔭 (v := v) hv hv𝔭
  have k𝔭' := range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (ζ ℓ)) 𝔭' h𝔭' (v := v₂) hv₂ hv𝔭'
  refine ⟨_, hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => h2 ?_⟩
  · rw [himg, himg']
    by_cases q1 : 𝔮 = 𝔭
    · rw [q1]; exact k𝔭.2
    by_cases q2 : 𝔮 = 𝔭'
    · rw [q2]; exact k𝔭'.2
    exact range_le_of_mem _ _ _ _ fun x => by
      rw [hℓx]
      exact add_mem (𝔮.mul_mem_right _ (he _ h𝔮 hn𝔮 q1)) (𝔮.mul_mem_right _ (he' _ h𝔮 hn𝔮 q2))
  · rw [himg'] at hle
    have hu := hle k𝔭.1
    have b1 : H.bar e ∈ 𝔭 := (hmem _).1 he𝔭'
    have b2 : H.bar e' - 1 ∈ 𝔭 := by simpa using (hmem _).1 he1'
    have : y (ζ ℓ') = y (ζ ℓ) - H.bar e • y (ζ ℓ₀) - (H.bar e' - 1) • y (ζ ℓ') := by
      rw [hℓdef, map_add, hζs, hζs, map_add, map_smul, map_smul, sub_smul, one_smul]; abel
    show y (ζ ℓ') ∈ img D y Z' 𝔭
    rw [this]
    exact sub_mem (sub_mem hu (Submodule.mem_sup_right (Submodule.smul_mem_smul b1 trivial)))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul b2 trivial))

end GlobalTheory.LowFilt
