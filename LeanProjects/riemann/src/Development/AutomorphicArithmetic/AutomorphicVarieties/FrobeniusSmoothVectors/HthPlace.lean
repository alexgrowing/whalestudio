import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hth_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring
    (Ideal.span {(⟨(p : Ω), natCast_mem _ p⟩ : (⊥ : Subring Ω))}) (by
      intro h
      rw [Ideal.span_singleton_eq_top] at h
      obtain ⟨⟨b, hb⟩, hb1⟩ := isUnit_iff_exists_inv.mp h
      obtain ⟨n, rfl⟩ := Subring.mem_bot.mp hb
      have h0 : ((p : Ω) * (n : Ω)) = 1 := congrArg Subtype.val hb1
      have h1 : ((p : ℤ) * n : ℤ) = 1 := by exact_mod_cast h0
      have h2 : (p : ℤ) ∣ 1 := ⟨n, h1.symm⟩
      have h3 : p ∣ 1 := by exact_mod_cast h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3))
  exact ⟨B, B.mem_nonunits_iff.mp (hB ⟨_, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hth_spec (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (w : ℕ) [hw : Fact w.Prime]
    (s : G ℚ Ω) (ζ : Ω) (h : ζ ^ w = 1) : s ζ = ζ ^ ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have h1 : ζ ^ w ^ 1 = 1 := by rwa [pow_one]
  exact cyclotomicCharacter.spec (L := Ω) w (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ h1

private theorem hth_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (w : ℕ) [hw : Fact w.Prime] (s : G ℚ Ω) :
    (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero w := ⟨hw.out.ne_zero⟩
  have hred : ∀ (ζ : Ω) (m : ℕ), ζ ^ w = 1 → ζ ^ m = ζ ^ (m % w) := by
    intro ζ m hζ
    conv_lhs => rw [← Nat.mod_add_div m w, pow_add, pow_mul, hζ, one_pow, mul_one]
  have hcv : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val < w :=
    lt_of_lt_of_eq (ZMod.val_lt _) (pow_one w)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω w
    have e1 := ha ζ0 hζ0.pow_eq_one
    rw [hth_spec Ω w s ζ0 hζ0.pow_eq_one, hred ζ0 (a ^ l) hζ0.pow_eq_one] at e1
    have e2 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)).val = a ^ l % w :=
      hζ0.pow_inj hcv (Nat.mod_lt _ (Nat.pos_of_neZero w)) e1
    have e3 : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) = (a : ZMod (w ^ 1)) ^ l := by
      apply ZMod.val_injective
      rw [e2, ← Nat.cast_pow, ZMod.val_natCast, pow_one]
    have hu : IsUnit (a : ZMod (w ^ 1)) := (isUnit_pow_iff hl0).mp (e3 ▸ (cycMod ℚ Ω w 1 s).isUnit)
    exact ⟨hu.unit, Units.ext (by simp [e3])⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u : ZMod (w ^ 1)).val, fun ζ hζ => ?_⟩
    have e : ((cycMod ℚ Ω w 1 s : (ZMod (w ^ 1))ˣ) : ZMod (w ^ 1)) =
        (((u : ZMod (w ^ 1)).val ^ l : ℕ) : ZMod (w ^ 1)) := by
      rw [← hu]
      simp
    rw [hth_spec Ω w s ζ hζ, hred ζ (((u : ZMod (w ^ 1)).val) ^ l) hζ, e, hred ζ _ hζ,
      ZMod.val_natCast, Nat.mod_mod_of_dvd _ (dvd_pow_self w one_ne_zero)]

theorem UpperTheory.V.Fr.hth :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (w : ℕ), w.Prime → w ≡ 1 [MOD l] → IsOpen (Hth Ω l w : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hth Ω l w ∧ (Hth Ω l w).index = l ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (w : Ω) < 1 → Ine (F := ℚ) B' ≤ Hth Ω l w) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (w : Ω) < 1 → ¬ Ine (F := ℚ) B' ≤ Hth Ω l w := by
  intro Ω _ _ _ l hl w hwp hw1
  haveI hw : Fact w.Prime := ⟨hwp⟩
  haveI : Fact (w ^ 1).Prime := ⟨by rw [pow_one]; exact hwp⟩
  have hmem : ∀ s : G ℚ Ω, s ∈ Hth Ω l w ↔
      cycMod ℚ Ω w 1 s ∈ (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range := by
    intro s
    change (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s ζ = ζ ^ a ^ l) ∧
      (∃ a : ℕ, ∀ ζ : Ω, ζ ^ w = 1 → s⁻¹ ζ = ζ ^ a ^ l) ↔ _
    rw [hth_iff Ω l w s, hth_iff Ω l w s⁻¹, map_inv, inv_mem_iff, and_self]
  have hker : (cycMod ℚ Ω w 1).ker ≤ Hth Ω l w := fun s hs =>
    (hmem s).mpr (by rw [MonoidHom.mem_ker.mp hs]; exact one_mem _)
  have hZ : ∀ s, cycMod ℚ Ω w 1 s = KStar.TotallyRealRoots.redPow w 1 (cycZ ℚ Ω w s) := fun s => rfl
  obtain ⟨A, hA⟩ := hth_place Ω w hwp
  have hsurj : Function.Surjective (cycMod ℚ Ω w 1) := by
    intro v
    obtain ⟨u, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 v
    obtain ⟨σ, -, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w A hA u
    exact ⟨σ, by rw [hZ, hσ]⟩
  have hidx : (Hth Ω l w).index = l := by
    have hH : Hth Ω l w =
        (powMonoidHom l : (ZMod (w ^ 1))ˣ →* (ZMod (w ^ 1))ˣ).range.comap (cycMod ℚ Ω w 1) := by
      ext s
      exact hmem s
    rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range,
      Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hwp]
    exact Nat.gcd_eq_right ((Nat.modEq_iff_dvd' hwp.one_lt.le).mp hw1.symm)
  refine ⟨?_, ?_, hidx, ?_, ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := (KStar.TotallyRealRoots.princ w 1).comap (cycZ ℚ Ω w)) ?_ ?_
    · intro s hs
      apply hker
      rw [MonoidHom.mem_ker, hZ]
      exact hs
    · exact (contTw ℚ Ω w).1.isOpen_preimage _ (KStar.TotallyRealRoots.isOpen_princ 1)
  · exact (Abelianization.commutator_subset_ker (cycMod ℚ Ω w 1)).trans hker
  · intro B' hB' s hs
    apply hker
    rw [MonoidHom.mem_ker, hZ, MonoidHom.mem_ker.mp ((places ℚ Ω w B').2.2.2 hB' hs), map_one]
  · intro B' hB' hle
    have htop : Hth Ω l w = ⊤ := by
      refine eq_top_iff.mpr fun s _ => ?_
      obtain ⟨u, hu⟩ := KStar.TotallyRealRoots.redPow_surjective (l := w) 1 (cycMod ℚ Ω w 1 s)
      obtain ⟨σ, hσI, hσ⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω w B' hB' u
      have h1 := (hmem σ).mp (hle hσI)
      rw [hZ, hσ, hu] at h1
      exact (hmem s).mpr h1
    rw [htop, Subgroup.index_top] at hidx
    exact hl.out.one_lt.ne hidx
