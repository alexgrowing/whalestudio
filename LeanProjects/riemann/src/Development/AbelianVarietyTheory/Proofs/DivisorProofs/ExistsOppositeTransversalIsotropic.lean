import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalIdealsContainingNatCastStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneModMaximalMemOtherMaximalsOverNatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupSmulTopEqTopOfForallMaximalOverNatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorMapsIntoIdealOfNotOntoModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFormFactorThroughTraceGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfOrthogoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankOneChangeImprovesImageRealPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOppositeSubmoduleImprovedModPrimeOfNeConjStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Transv

theorem fin_max : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite :=
  GlobalTheory.T.finite_maximal_ideals_containing_natCast'

theorem exists_sep : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 :=
  GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat

theorem sup_eq_top : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ :=
  GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat

theorem exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 :=
  GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod

theorem exists_real_theta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) :=
  GlobalTheory.T.exists_conj_invariant_trace_generator_local

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ :=
  GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal

theorem improves_A : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal

theorem rankOneChange_improves_real_prime_first : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_rankOneChange_improves_image_real_prime

theorem rankOneChange_improves_nonreal_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
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
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj

theorem img_top_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hc : Cois D y n)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hZ : Z.map y ≤ img D y Z' 𝔭) (hL : ∀ m ∈ perp D Z ⊓ perp D Z', y m ∈ img D y Z' 𝔭) :
    img D y Z' 𝔭 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, e, hae⟩ := hc.1 x
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp a
  have h1 : y (z + m + b) ∈ img D y Z' 𝔭 := by
    rw [map_add, map_add]
    exact add_mem (add_mem (hZ ⟨z, hz, rfl⟩) (hL m hm)) (Submodule.mem_sup_left ⟨b, hb, rfl⟩)
  have h2 : n • e ∈ img D y Z' 𝔭 := by
    apply Submodule.mem_sup_right
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hn𝔭 trivial
  have h3 : x = y (z + m + b) - n • e := by rw [hae]; abel
  rw [h3]
  exact sub_mem h1 h2

theorem improve {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) : ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨e, he1, he⟩ := exists_sep (E := E) n hn 𝔭 h𝔭
  obtain ⟨v, hv, ℓ₀, hℓ₀⟩ := exists_ker_vec D y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨θ, hθ, s, hs, hs', hgen⟩ := exists_real_theta H 𝔭 h𝔭
  by_cases hA : ∃ m ∈ perp D Z ⊓ perp D Z', y m ∉ img D y Z' 𝔭 ∧
      (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭)
  · obtain ⟨m, hm, hym, hA⟩ := hA
    exact improves_A D y n Z Z' h 𝔭 h𝔭 hn𝔭 e he1 he v hv ℓ₀ hℓ₀ m hm hym hA
  have hZ : ¬ Z.map y ≤ img D y Z' 𝔭 := fun hZ =>
    hi (img_top_of D y n hc Z Z' h 𝔭 hn𝔭 hZ fun m hm => by_contra fun h' => hA ⟨m, hm, h', Or.inr hZ⟩)
  by_cases hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭
  · exact rankOneChange_improves_real_prime_first D y n Z Z' h 𝔭 h𝔭 hb e he1 he v hv ℓ₀ hℓ₀ θ hθ s hs hs' hgen hZ
  have hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭 := by
    rintro _ ⟨m, hm, rfl⟩
    exact by_contra fun h' => hA ⟨m, hm, h', Or.inl hb⟩
  have hi' := img_bar_ne_top D y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL
  have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
  have hn𝔭' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
  obtain ⟨e', he1', he'⟩ := exists_sep (E := E) n hn _ h𝔭'
  obtain ⟨v₂, hv₂, ℓ₁, hℓ₁⟩ := exists_ker_vec D y Z Z' h hr _ h𝔭' hi'
  exact rankOneChange_improves_nonreal_prime D y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ

end GlobalTheory.LowFilt.Transv

namespace GlobalTheory.LowFilt

open GlobalTheory.LowFilt.Transv in
theorem exists_opp_transv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z₀ h0 hr
  classical
  let S := {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}
  haveI : Finite S := (fin_max (E := E) n hn).to_subtype
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  let F : Submodule (𝓞 E) D.La → (S → Submodule (𝓞 E) X) := fun Z' q => img D y Z' q.1
  haveI : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) X
  have h1 : WellFoundedLT (S → (Submodule (𝓞 E) X)ᵒᵈ) := Pi.wellFoundedLT
  haveI : WellFoundedGT (S → Submodule (𝓞 E) X) := ⟨h1.wf⟩
  have wf : WellFounded (fun a b : S → Submodule (𝓞 E) X => b < a) := wellFounded_gt
  obtain ⟨_, ⟨Z', hZ', rfl⟩, hmax⟩ := wf.has_min (F '' {Z' | IsOpp D Z Z'}) ⟨_, Z₀, h0, rfl⟩
  have htop : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 →
      Z'.map y ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
    intro 𝔮 hq hnq
    by_contra hne
    obtain ⟨Z'', h1, h2, h3⟩ := improve D y n hn hc Z Z' hZ' hr 𝔮 hq hnq hne
    exact hmax (F Z'') ⟨Z'', h1, rfl⟩
      (lt_of_le_not_ge (fun q => h2 q.1 q.2.1 q.2.2) fun hle => h3 (hle ⟨𝔮, hq, hnq⟩))
  have hall := sup_eq_top (Z'.map y) n hn htop
  refine ⟨Z', hZ', fun x => ?_⟩
  have hx : x ∈ Z'.map y ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) := by rw [hall]; trivial
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup] at hx
  obtain ⟨_, ⟨b, hb, rfl⟩, w, hw, hsum⟩ := hx
  obtain ⟨e', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  refine ⟨b, hb, -e', ?_⟩
  rw [smul_neg, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hsum]
  abel

end GlobalTheory.LowFilt
