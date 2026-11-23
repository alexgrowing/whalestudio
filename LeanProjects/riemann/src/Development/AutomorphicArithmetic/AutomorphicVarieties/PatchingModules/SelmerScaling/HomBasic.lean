import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.homBasic :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0), Function.Surjective h.p₀ ∧ Continuous h.p₀ ∧ (∀ g, h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g)) ∧ (∀ v g, h.p₀ (G.φ v g) = G0.φ v g) ∧ (∀ w, ∀ g ∈ G.frame.Iu w, h.p₀ g ∈ G0.frame.Iu w) ∧ ∀ (O R : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (g : G.G₀), G0.frame.eps O R (h.p₀ g) = G.frame.eps O R g := by
  intro l _ L G G0 h
  refine ⟨fun g => ?_, (h.cont.comp continuous_subtype_val).subtype_mk _, fun g => Subtype.ext ?_,
    fun v g => Subtype.ext (h.φ v g), ?_, fun O R _ _ _ _ g => ?_⟩
  · obtain ⟨a, ha⟩ := h.surj g
    exact ⟨⟨a, by rw [MonoidHom.mem_ker, ← h.η, ha]; exact g.2⟩, Subtype.ext ha⟩
  · change h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
  · rintro w _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, Subtype.ext (h.φu w j).symm⟩
  · change Units.map _ (G0.ε (h.p g)) = Units.map _ (G.ε g)
    rw [h.ε]
