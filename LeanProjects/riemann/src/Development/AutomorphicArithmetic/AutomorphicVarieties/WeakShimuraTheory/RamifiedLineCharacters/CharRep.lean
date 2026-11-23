import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.locNe :
    LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) → ∃ f ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), f ≠ 0 := by
  intro _ hE F Ω _ _ _ _ _ l _ A v hA hl _
  set ρ := Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) with hρ
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : (Dec (F := F) A) × ZMod (l ^ 1) => (ρ p.1) p.2
    simpa [hρ] using continuous_snd
  have hE' := (hE F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hcont).2 hl
  have h0 : Nat.card ↥(ReciprocityTheory.Gal.H0 ρ) = l := by
    have htop : ReciprocityTheory.Gal.H0 ρ = ⊤ := by
      ext x
      simp [ReciprocityTheory.Gal.H0, hρ]
    rw [htop, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_zmod, pow_one]
  by_contra hne
  push_neg at hne
  haveI hz : Subsingleton ↥(ReciprocityTheory.Gal.Z1 ρ) :=
    ⟨fun a b => Subtype.ext ((hne a a.2).trans (hne b b.2).symm)⟩
  haveI hs : Subsingleton (ReciprocityTheory.Gal.H1 ρ) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  have h1 : Nat.card (ReciprocityTheory.Gal.H1 ρ) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨0⟩⟩
  rw [h1, h0] at hE'
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hE'.symm)
