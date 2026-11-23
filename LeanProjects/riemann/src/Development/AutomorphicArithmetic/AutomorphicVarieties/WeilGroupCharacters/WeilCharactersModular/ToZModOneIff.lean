import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.W

private theorem toZMod_one_iff {l : ℕ} [Fact l.Prime] (x : ℤ_[l]) :
    PadicInt.toZMod x = 1 ↔ PadicInt.toZModPow 1 x = 1 := by
  rw [← map_one (PadicInt.toZMod (p := l)), ← map_one (PadicInt.toZModPow (p := l) 1), ← RingHom.sub_mem_ker_iff,
    ← RingHom.sub_mem_ker_iff, PadicInt.ker_toZMod, PadicInt.ker_toZModPow, PadicInt.maximalIdeal_eq_span_p, pow_one]

private theorem fix_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] {ζ : Ω} (hζ : IsPrimitiveRoot ζ l) (x : ℤ_[l]) :
    ζ ^ (PadicInt.toZModPow 1 x).val = ζ ↔ PadicInt.toZMod x = 1 := by
  have h1 : 1 < l ^ 1 := by simpa using (Fact.out : l.Prime).one_lt
  haveI : Fact (1 < l ^ 1) := ⟨h1⟩
  haveI : NeZero (l ^ 1) := ⟨by omega⟩
  rw [toZMod_one_iff]
  constructor
  · intro h
    apply ZMod.val_injective
    rw [ZMod.val_one]
    refine hζ.pow_inj ?_ (Fact.out : l.Prime).one_lt (by rw [h, pow_one])
    simpa using ZMod.val_lt (PadicInt.toZModPow 1 x)
  · intro h
    rw [h, ZMod.val_one, pow_one]

theorem UpperTheory.V.W.muL :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V : s.Lev), (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) ↔ ∃ g : V.frame.G₀, PadicInt.toZMod ((V.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois L Ω := ⟨⟩
  have hε : ∀ σ : G L Ω, V.ε (V.pr σ).1 = cycZ (Lp L) Ω l (resP L Ω σ) := fun σ =>
    DFunLike.congr_fun V.hε (resP L Ω σ)
  have key : ∀ (σ : G L Ω) (ζ : Ω), IsPrimitiveRoot ζ l →
      (σ ζ = ζ ↔ PadicInt.toZMod ((V.ε (V.pr σ).1 : ℤ_[l]ˣ) : ℤ_[l]) = 1) := fun σ ζ hζ => by
    have h : σ ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ (Lp L) Ω l (resP L Ω σ) : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (Ω ≃ₐ[Lp L] Ω) Ω (resP L Ω σ)) ζ
        (by rw [pow_one, hζ.pow_eq_one])
    rw [hε, h, fix_iff hζ]
  have hsurj : ∀ g : V.η.ker, ∃ σ : G L Ω, V.pr σ = g := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  change _ ↔ ∃ g : V.η.ker, PadicInt.toZMod ((V.ε g.1 : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1
  constructor
  · intro hn
    by_contra hc
    push Not at hc
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
    have hm : ζ ∈ (⊥ : IntermediateField L Ω) := by
      rw [InfiniteGalois.mem_bot_iff_fixed]
      exact fun σ => (key σ ζ hζ).2 (hc _)
    obtain ⟨z, rfl⟩ := IntermediateField.mem_bot.1 hm
    exact hn ⟨z, hζ.of_map_of_injective (algebraMap L Ω).injective⟩
  · rintro ⟨g, hg⟩ ⟨z, hz⟩
    obtain ⟨σ, rfl⟩ := hsurj g
    exact hg ((key σ _ (hz.map_of_injective (algebraMap L Ω).injective)).1 (σ.commutes z))
