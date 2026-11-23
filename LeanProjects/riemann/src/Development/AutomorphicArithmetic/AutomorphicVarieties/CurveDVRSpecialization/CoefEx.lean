import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCoefOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV

private theorem ce_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem ce_char {l : ℕ} [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] (ka : Γ →* (PadicAlgCl l)ˣ) (h : Continuous ka) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ g, (ka g).val ∈ E ∧ ‖(ka g).val‖ ≤ 1 := by
  have hc : Continuous fun g => (ka g).val := Units.continuous_val.comp h
  let r : Γ →* GL (Fin 1) (PadicAlgCl l) :=
    (Units.map (Matrix.scalar (Fin 1) : PadicAlgCl l →+* _).toMonoidHom).comp ka
  have hr : ∀ (g : Γ) (i j : Fin 1), (r g).val i j = (ka g).val := by
    intro g i j
    obtain rfl : i = j := Subsingleton.elim _ _
    simp [r]
  obtain ⟨E, hE, hm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 1 r
    (fun i j => by simp only [hr]; exact hc)
  refine ⟨E, hE, fun g => ⟨hr g 0 0 ▸ hm g 0 0, ?_⟩⟩
  obtain ⟨C, hC⟩ := (isCompact_range hc.norm).bddAbove
  by_contra hg
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (not_le.1 hg)
  have := hC ⟨g ^ N, rfl⟩
  simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
  exact absurd hN (not_lt.2 this)

private theorem ce_fin {l : ℕ} [Fact l.Prime] (s : Set (PadicAlgCl l)) (hs : s.Finite) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) := by
  haveI := hs.to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

private theorem ce_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x : c.O, x.1 ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := c.O)
  refine ⟨IntermediateField.adjoin ℚ_[l] (Subtype.val '' (s : Set c.O)), ce_fin _ (s.finite_toSet.image _), fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul a b _ hb =>
    rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] a]
    exact IntermediateField.smul_mem _ hb

private theorem ce_large {l : ℕ} [Fact l.Prime] (L : Type) [Field L] [NumberField L] :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧
      ∀ (τ : L →+* PadicAlgCl l) (x : L), τ x ∈ E := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℚ) (M := L)
  refine ⟨IntermediateField.adjoin ℚ_[l] (⋃ τ : L →+* PadicAlgCl l, τ '' (s : Set L)),
    ce_fin _ (Set.finite_iUnion fun τ => s.finite_toSet.image _), fun τ x => ?_⟩
  have hx : x ∈ Submodule.span ℚ (s : Set L) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact IntermediateField.subset_adjoin _ _ (Set.mem_iUnion.2 ⟨τ, y, hy, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a b _ hb =>
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ a) hb

theorem UpperTheory.V.Pr.coefEx :
    UpperTheory.V.Pr.CoefEx := by
  intro l _ c L Ω _ _ _ _ _ ka ka' h h'
  haveI : CompactSpace (G L Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[L] Ω))
  haveI : T2Space (G L Ω) := inferInstanceAs (T2Space (Ω ≃ₐ[L] Ω))
  obtain ⟨E₁, f₁, m₁⟩ := ce_char (G L Ω) ka h
  obtain ⟨E₂, f₂, m₂⟩ := ce_char (G L Ω) ka' h'
  obtain ⟨E₃, f₃, m₃⟩ := ce_coef c
  obtain ⟨E₄, f₄, m₄⟩ := ce_large (l := l) L
  obtain ⟨c₁, hc⟩ := UpperTheory.V.X.So.coefOf l ((E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄))
  have l₁ : E₁ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_left
  have l₂ : E₂ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_left le_sup_right
  have l₃ : E₃ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_left
  have l₄ : E₄ ≤ (E₁ ⊔ E₂) ⊔ (E₃ ⊔ E₄) := le_sup_of_le_right le_sup_right
  have hle : c.O ≤ c₁.O := fun x hx => (hc x).2 ⟨l₃ (m₃ ⟨x, hx⟩),
    ce_norm x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)⟩
  refine ⟨c₁, hle, fun τ x => (hc _).2 ⟨l₄ (m₄ τ x), ce_norm _ ?_⟩, fun g => (hc _).2 ⟨l₁ (m₁ g).1, (m₁ g).2⟩,
    fun g => (hc _).2 ⟨l₂ (m₂ g).1, (m₂ g).2⟩, ?_⟩
  · exact (x.isIntegral_coe.map τ.toIntAlgHom).tower_top
  · let φ : c.O →+* c₁.O := (Subalgebra.inclusion hle).toRingHom
    have hint : φ.IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) φ ?_
      have e : φ.comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c₁.O := (Subalgebra.inclusion hle).comp_algebraMap
      rw [e]
      exact fun x => Algebra.IsIntegral.isIntegral x
    haveI : IsLocalHom φ := hint.isLocalHom (Subalgebra.inclusion_injective hle)
    refine ⟨ResidueField.map φ, fun a b hab => ?_⟩
    rw [ResidueField.map_residue]
    exact congrArg _ (Subtype.ext hab)
