import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.noMu :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}, D.Good → ∀ (L : IntermediateField ℚ Ω) (g : G L Ω), Raw.bar D.om (resQ L g) ≠ 1 → ¬ ∃ ζ : L, IsPrimitiveRoot ζ l := by
  intro Ω _ _ _ l _ c D hD L g hbar hroot
  obtain ⟨ζ, hζ⟩ := hroot
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  haveI := c.fin
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hζΩ : IsPrimitiveRoot (ζ : Ω) l := hζ.map_of_injective (L.val : L →+* Ω).injective
  set σ : G ℚ Ω := resQ L g with hσ
  set χ : ℤ_[l] := ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) with hχ
  have hfix : (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) = (ζ : Ω) := g.commutes ζ
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := 1)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (ζ : Ω) (by rw [pow_one]; exact hζΩ.pow_eq_one)
  rw [hfix] at hspec
  have hmod : PadicInt.toZModPow 1 χ = 1 := by
    haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl⟩
    apply ZMod.val_injective
    rw [ZMod.val_one]
    have hlt : (PadicInt.toZModPow 1 χ).val < l :=
      lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow 1 χ)) (pow_one l)
    apply hζΩ.pow_inj hlt hl
    exact hspec.symm.trans (pow_one _).symm
  have hmem : χ - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]), ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, hmod, map_one, sub_self]
  have hnu : algebraMap ℤ_[l] c.O (χ - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu)
  apply hbar
  rw [hD.om_bar]
  change IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O χ) = 1
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, map_one] at hnu
  exact sub_eq_zero.mp hnu
