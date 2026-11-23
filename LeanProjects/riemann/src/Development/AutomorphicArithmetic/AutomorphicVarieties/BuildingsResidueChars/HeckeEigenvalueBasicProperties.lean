import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem algSat_injective (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ)
    (h : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B') : B = B' := by
  unfold UpperTheory.V.Af.algSat at h
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((n : ℝ) - 1) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    exact_mod_cast this.ne'
  have h1 := Multiset.map_injective (mul_right_injective₀ hc) h
  have h2 : ∀ s : Multiset ℂˣ, (do let a ← s; pure (a : ℂ)) =
      Multiset.map (fun a : ℂˣ => (a : ℂ)) s := fun s => Multiset.bind_singleton _ _
  rw [h2, h2] at h1
  exact Multiset.map_injective Units.val_injective h1

theorem UpperTheory.hecke_eigenvalue_basic_properties :
    UpperTheory.V.Af.Sol.EigBasic := by
  intro F Ω _ _ _ _ _ l _ ι v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  refine ⟨?_, ?_, ?_⟩
  · intro δ δ' z z' hz hz' A' hA'
    obtain ⟨hi, hf⟩ := hz A' hA'
    obtain ⟨hi', hf'⟩ := hz' A' hA'
    refine ⟨fun s hs => ?_, fun τ hτ => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi s hs, hi' s hs, inv_one, mul_one]
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Units.val_inv_eq_inv_val,
        map_inv₀, hf τ hτ, hf' τ hτ]
      push_cast
      rfl
  · intro δ z z' hz hz'
    apply Units.ext
    rw [← (hz A hA).2 σ hσ, ← (hz' A hA).2 σ hσ]
  · intro n r B B' hB hB'
    have e1 := (hB A hA).2 σ hσ
    have e2 := (hB' A hA).2 σ hσ
    rw [e1] at e2
    have e3 := congrArg Polynomial.roots e2
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
    have hq : Formalism.ConjugateSelfDual.normV v ≠ 0 := by
      unfold Formalism.ConjugateSelfDual.normV
      exact Nat.card_pos.ne'
    exact algSat_injective n _ hq B B' e3
