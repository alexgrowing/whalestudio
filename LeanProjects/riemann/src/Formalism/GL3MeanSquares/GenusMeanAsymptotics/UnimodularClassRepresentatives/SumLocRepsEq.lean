import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrB

section One

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem akCount_congr {A B : Submodule (𝓞 K) V} (e : ↥A ≃ₗ[𝓞 K] ↥B)
    (he : ∀ x y : ↥A, h (e x : V) (e y : V) = h (x : V) (y : V)) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    akCount h B 𝔭 k = akCount h A 𝔭 k := by
  have hmap : ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A).map (e : ↥A →ₗ[𝓞 K] ↥B) =
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let ε := Submodule.Quotient.equiv _ _ e hmap
  have hε : ∀ x : ↥A, ε (Submodule.Quotient.mk x) = Submodule.Quotient.mk (e x) := fun x => rfl
  unfold akCount
  refine (Nat.card_congr (Equiv.subtypeEquiv ε.conj.toEquiv ?_)).symm
  intro X
  have hX : ∀ x : ↥A, (ε.conj X) (Submodule.Quotient.mk (e x)) = ε (X (Submodule.Quotient.mk x)) := by
    intro x
    rw [LinearEquiv.conj_apply_apply, ← hε, LinearEquiv.symm_apply_apply]
  constructor
  · intro H x y x' y' h1 h2
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective x'
    obtain ⟨y', rfl⟩ := e.surjective y'
    rw [he, he]
    refine H x y x' y' ?_ ?_
    · apply ε.injective
      rw [hε, ← hX]
      exact h1
    · apply ε.injective
      rw [hε, ← hX]
      exact h2
  · intro H x y x' y' h1 h2
    rw [← he, ← he x y]
    refine H (e x) (e y) (e x') (e y') ?_ ?_
    · change _ = (ε.conj X) _
      rw [hX, ← h1, hε]
    · change _ = (ε.conj X) _
      rw [hX, ← h2, hε]

theorem akCount_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (k : ℕ) : akCount h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 k = akCount h T 𝔭 k :=
  akCount_congr (A := T) (B := Formalism.HermitianLatticesTheory.gmap g T) ((g.restrictScalars (𝓞 K)).submoduleMap T)
    (fun x y => hg (x : V) (y : V)) 𝔭 k

theorem alphaL_gmap {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : alphaL h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = alphaL h T 𝔭 := by
  unfold alphaL
  simp only [akCount_gmap hg]

end One

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem localFactor_map' {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : lamP h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = lamP h T 𝔭 := by
  unfold lamP
  rw [UnimodularLocalization.vd_gmap hg, alphaL_gmap hg]

theorem sum_locReps_eq (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s s' : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s)
    (hsr' : IsLocReps S L 𝔭 s') :
    ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 = ∑ T ∈ s', (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have ex : ∀ T ∈ s, ∃! T₀, T₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T :=
    fun T hT => hsr'.2 T (hsr.1 T hT).1 (hsr.1 T hT).2.1 (hsr.1 T hT).2.2
  refine Finset.sum_bij (fun T hT => (ex T hT).choose) ?_ ?_ ?_ ?_
  · exact fun T hT => (ex T hT).choose_spec.1.1
  · intro T₁ h1 T₂ h2 e
    obtain ⟨g₁, hg₁, e₁⟩ := (ex T₁ h1).choose_spec.1.2
    obtain ⟨g₂, hg₂, e₂⟩ := (ex T₂ h2).choose_spec.1.2
    simp only at e
    rw [← e] at e₂
    have hu := hsr.2 T₂ (hsr.1 T₂ h2).1 (hsr.1 T₂ h2).2.1 (hsr.1 T₂ h2).2.2
    refine hu.unique ⟨h1, g₂ * g₁⁻¹, Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁), ?_⟩
      ⟨h2, 1, Subgroup.one_mem _, autSub_gmap_one _⟩
    rw [← e₁, ← autSub_gmap_mul, mul_assoc, inv_mul_cancel, mul_one, e₂]
  · intro T₀ h0
    obtain ⟨T, ⟨hT, g, hg, e⟩, -⟩ :=
      hsr.2 T₀ (hsr'.1 T₀ h0).1 (hsr'.1 T₀ h0).2.1 (hsr'.1 T₀ h0).2.2
    refine ⟨T, hT, ?_⟩
    refine (ex T hT).unique (ex T hT).choose_spec.1 ⟨h0, g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    rw [← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro T hT
    obtain ⟨g, hg, e⟩ := (ex T hT).choose_spec.1.2
    conv_lhs => rw [← e, GoodGenusOrbits.fibLoc_gmap hs S L 𝔭 hg, localFactor_map' hg]

theorem psiP_eq_sum' (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by
  have hex : ∃ s, IsLocReps S L 𝔭 s := ⟨s, hsr⟩
  unfold psiP
  rw [dif_pos hex]
  exact sum_locReps_eq hs S L 𝔭 hex.choose_spec hsr

end Formalism.HermitianLattices.Ext.L3.BrB
