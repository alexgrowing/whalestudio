import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BaseCh

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private def sigSub {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    Submodule R ((Σ v, X v) → R) where
  carrier := {z | ∀ v, (fun s => z ⟨v, s⟩) ∈ p v}
  add_mem' ha hb v := (p v).add_mem (ha v) (hb v)
  zero_mem' v := (p v).zero_mem
  smul_mem' c _ ha v := (p v).smul_mem c (ha v)

private def sigEquiv {ι R : Type} {X : ι → Type} [CommRing R] (p : ∀ v, Submodule R (X v → R)) :
    (∀ v, p v) ≃ₗ[R] sigSub p where
  toFun f := ⟨fun x => (f x.1).1 x.2, fun v => (f v).2⟩
  invFun z v := ⟨fun s => z.1 ⟨v, s⟩, z.2 v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem phi_mul {k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (φ : k →ₗ[k₀] k₀) (x : k₀) (y : k) :
    φ (algebraMap k₀ k x * y) = x * φ y := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem zgl_phi {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k₀ k : Type} [Field k₀]
    [Field k] [Algebra k₀ k] (a₀ : O →+* k₀) (w : ℤ × ℤ) (z : Γ → k) (hz : z ∈ Φ.Zgl ((algebraMap k₀ k).comp a₀) w)
    (φ : k →ₗ[k₀] k₀) : (fun x => φ (z x)) ∈ Φ.Zgl a₀ w := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  refine ⟨h1.comp φ, fun g h => ?_, fun g h => ?_, fun h => ?_⟩
  · show φ (z (g * h)) = φ (z g) + _ * φ (z h)
    rw [h2, map_add, RingHom.comp_apply, phi_mul]
  · show φ (z g) = 0
    rw [h3 g h, map_zero]
  · show φ (z Φ.g0) = 0
    rw [h4 h, map_zero]

theorem UpperTheory.V.Ws.cocycleBounds_of_ringHom_comp :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) (k₀ k : Type) [Field k₀] [Field k] (a₀ : O →+* k₀) (j : k₀ →+* k) (d C : ℕ), Φ.Bounds a₀ d C → Φ.Bounds (j.comp a₀) d C := by
  intro O Γ _ _ _ Φ k₀ k _ _ a₀ j d C hB
  letI : Algebra k₀ k := j.toAlgebra
  change Φ.Bounds ((algebraMap k₀ k).comp a₀) d C
  refine ⟨hB.card, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · refine rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.str w hw) ?_
    rintro z ⟨hz, n, hn⟩ φ
    refine ⟨zgl_phi Φ a₀ w z hz φ, fun v => φ (n v), fun v s hs => ?_⟩
    show φ (z s) = φ (n v) - _ * φ (n v)
    rw [hn v s hs, map_sub, RingHom.comp_apply, phi_mul]
  · exact rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ C (hB.even w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
  · have := rank_le_of_linearForm_comp_mem_of_rank_le Γ k₀ k _ _ (d + C) (by exact_mod_cast hB.odd w hw) fun z hz φ => zgl_phi Φ a₀ w z hz φ
    exact_mod_cast this
  · have h0 := hB.loc w hw
    rw [(sigEquiv _).rank_eq] at h0 ⊢
    have := rank_le_of_linearForm_comp_mem_of_rank_le _ k₀ k _ (sigSub fun v => Φ.Zloc ((algebraMap k₀ k).comp a₀) (Φ.Gv v) w) (d + C)
      (by exact_mod_cast h0) (by
        intro z hz φ v
        obtain ⟨h1, h2⟩ := hz v
        refine ⟨h1.comp φ, fun g h => ?_⟩
        have h3 := congrArg φ (h2 g h)
        rw [map_add, RingHom.comp_apply, phi_mul] at h3
        exact h3)
    exact_mod_cast this
