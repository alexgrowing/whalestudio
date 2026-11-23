import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem continuous_to_torsion_bounded {G : Type} [TopologicalSpace G] [CompactSpace G] (l : ℕ) [Fact l.Prime]
    (f : G → QZ l) (hf : Continuous f) : ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • f g = 0 := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  choose k hk using (UpperTheory.V.Kum.qzBasic l).2.1
  obtain ⟨r, hr⟩ := (hfin.image k).bddAbove
  refine ⟨r, fun g => ?_⟩
  have h1 : k (f g) ≤ r := hr ⟨f g, ⟨g, rfl⟩, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have h2 : (l : ℤ_[l]) ^ k (f g) • f g = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hk _
  rw [pow_add, mul_smul, h2, smul_zero]

theorem UpperTheory.V.Odd.Z1_H1_qz_twist_l_power_torsion :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), (∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ x : H1 (qzTw D e), ∃ r : ℕ, (l : ℤ_[l]) ^ r • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e
  have h : ∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0 := fun z =>
    continuous_to_torsion_bounded l z.1 z.2.1
  refine ⟨h, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨r, hr⟩ := h z
  refine ⟨r, ?_⟩
  have hz : (l : ℤ_[l]) ^ r • z = 0 := Subtype.ext (funext hr)
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]
