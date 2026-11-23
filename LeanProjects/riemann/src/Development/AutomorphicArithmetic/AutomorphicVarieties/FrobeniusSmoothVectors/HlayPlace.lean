import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem hlay_place (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hmem : (p : Ω) ∈ (⊥ : Subring Ω) := Subring.mem_bot.mpr ⟨p, by simp⟩
  set x : (⊥ : Subring Ω) := ⟨p, hmem⟩
  have hI : Ideal.span {x} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb⟩ := Subring.mem_bot.mp (u⁻¹ : (⊥ : Subring Ω)ˣ).1.2
    have h1 : (u : (⊥ : Subring Ω)) * (↑u⁻¹ : (⊥ : Subring Ω)) = 1 := u.mul_inv
    have h2 : ((p : ℤ) * b : ℤ) = (1 : Ω) := by
      have := congrArg Subtype.val h1
      simp only [Subring.coe_mul, Subring.coe_one] at this
      rw [hu] at this
      push_cast
      rw [hb]
      exact this
    have h3 : (p : ℤ) * b = 1 := by exact_mod_cast h2
    have h4 : (p : ℤ) ∣ 1 := ⟨b, h3.symm⟩
    have : p ∣ 1 := by exact_mod_cast h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨B, (ValuationSubring.mem_nonunits_iff B).mp (hB ⟨x, Ideal.subset_span rfl, rfl⟩)⟩

private theorem hlay_cop (l : ℕ) [hl : Fact l.Prime] (m : ℕ) : (l ^ m).Coprime (l - 1) := Nat.Coprime.pow_left m ((Nat.coprime_self_sub_right hl.out.one_le).mpr (Nat.coprime_one_right _))

private theorem hlay_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (h2 : l ≠ 2) :
    Nat.card ((⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1))) = l ^ m := by
  haveI := ZMod.isCyclic_units_of_prime_pow l hl.out h2 (m + 1)
  rw [← MonoidHom.range_eq_map, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out]
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  rw [Nat.gcd_comm, Nat.gcd_mul_left_right]
  exact Nat.mul_div_cancel _ hpos

private theorem hlay_inf {l : ℕ} [hl : Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) (h1 : u ∈ KStar.TotallyRealRoots.princ l 1)
    (h : KStar.TotallyRealRoots.redPow l (m + 1) u ^ (l - 1) = 1) : KStar.TotallyRealRoots.redPow l (m + 1) u = 1 := by
  set x := KStar.TotallyRealRoots.redPow l (m + 1) u with hx
  have hd : l ^ 1 ∣ l ^ (m + 1) := pow_dvd_pow l (by omega)
  set f := ZMod.unitsMap hd
  have hfx : f x = 1 := by
    have : f x = KStar.TotallyRealRoots.redPow l 1 u := by
      ext
      simp only [f, hx, ZMod.unitsMap, KStar.TotallyRealRoots.redPow, Units.coe_map, MonoidHom.coe_coe]
      exact congrArg (fun g => g (u : ℤ_[l])) (PadicInt.zmod_cast_comp_toZModPow 1 (m + 1) (by omega))
    rw [this]
    exact h1
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hd
  have hcardG : Nat.card (ZMod (l ^ (m + 1)))ˣ = l ^ m * (l - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ hl.out]
  have hcardH : Nat.card (ZMod (l ^ 1))ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hl.out]
  have hker : Nat.card f.ker = l ^ m := by
    have e := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcardH, hcardG] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hl.out.one_lt) e
  have hpow : x ^ (l ^ m) = 1 := by
    have := pow_card_eq_one' (G := f.ker) (x := ⟨x, hfx⟩)
    rw [hker] at this
    exact congrArg Subtype.val this
  have hdvd : orderOf x ∣ Nat.gcd (l ^ m) (l - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_of_pow_eq_one h)
  rw [hlay_cop l m, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem UpperTheory.V.Fr.hlay :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ), l ≠ 2 → IsOpen (Hlay Ω l m : Set (G ℚ Ω)) ∧ commutator (G ℚ Ω) ≤ Hlay Ω l m ∧ (Hlay Ω l m).index = l ^ m ∧ Hlay Ω l m ⊓ (cycMod ℚ Ω l 1).ker = (cycMod ℚ Ω l (m + 1)).ker ∧ (∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → Ine (F := ℚ) B' ≤ Hlay Ω l m) ∧ ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → (Hlay Ω l m).relIndex (Ine (F := ℚ) B') = l ^ m ∧ ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
  intro Ω _ _ _ l _ m h2
  obtain ⟨A, hA⟩ := hlay_place Ω l Fact.out
  have hsurjIne : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 →
      ∀ r, (Ine (F := ℚ) B').map (cycMod ℚ Ω l r) = ⊤ := by
    intro B' hB' r
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := KStar.TotallyRealRoots.redPow_surjective (l := l) r y
    obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l B' hB' v
    exact ⟨σ, hσ, by rw [← hσv]; rfl⟩
  have hidx : ∀ K : Subgroup (G ℚ Ω), K.map (cycMod ℚ Ω l (m + 1)) = ⊤ →
      (Hlay Ω l m).relIndex K = l ^ m := by
    intro K hK
    have hsub : (Hlay Ω l m).subgroupOf K = ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).ker := by
      ext x
      rfl
    rw [Subgroup.relIndex, hsub, Subgroup.index_ker]
    have hr : ((cycMod ℚ Ω l (m + 1) ^ (l - 1)).comp K.subtype).range =
        (⊤ : Subgroup (ZMod (l ^ (m + 1)))ˣ).map (powMonoidHom (l - 1)) := by
      ext y
      simp only [MonoidHom.mem_range, Subgroup.mem_map, Subgroup.mem_top, true_and, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MonoidHom.pow_apply, powMonoidHom_apply]
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨z, rfl⟩
        have hz : z ∈ K.map (cycMod ℚ Ω l (m + 1)) := hK ▸ Subgroup.mem_top z
        obtain ⟨k, hk, rfl⟩ := hz
        exact ⟨⟨k, hk⟩, rfl⟩
    rw [hr]
    exact hlay_card l m h2
  have hcont := (UpperTheory.V.Base.contTw ℚ Ω l).1
  have hkerle : (cycMod ℚ Ω l (m + 1)).ker ≤ Hlay Ω l m := by
    intro σ hσ
    show (cycMod ℚ Ω l (m + 1) σ) ^ (l - 1) = 1
    rw [MonoidHom.mem_ker.mp hσ, one_pow]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun B' hB' => ⟨hidx _ (hsurjIne B' hB' _), hsurjIne B' hB'⟩⟩
  · apply Subgroup.isOpen_mono hkerle
    have hset : ((cycMod ℚ Ω l (m + 1)).ker : Set (G ℚ Ω)) =
        cycZ ℚ Ω l ⁻¹' (KStar.TotallyRealRoots.princ l (m + 1) : Set ℤ_[l]ˣ) := by
      ext σ
      rfl
    rw [hset]
    exact (KStar.TotallyRealRoots.isOpen_princ (m + 1)).preimage hcont
  · exact Abelianization.commutator_subset_ker _
  · rw [← Subgroup.relIndex_top_right]
    exact hidx ⊤ (top_unique ((hsurjIne A hA _).symm.le.trans (Subgroup.map_mono le_top)))
  · apply le_antisymm
    · rintro σ ⟨h1, h1'⟩
      exact hlay_inf m (cycZ ℚ Ω l σ) h1' h1
    · intro σ hσ
      exact ⟨hkerle hσ, KStar.TotallyRealRoots.princ_anti (by omega) hσ⟩
  · intro B' hB'
    refine ((UpperTheory.V.Base.places ℚ Ω l B').2.2.2 hB').trans ?_
    intro σ hσ
    apply hkerle
    show KStar.TotallyRealRoots.redPow l (m + 1) (cycZ ℚ Ω l σ) = 1
    rw [MonoidHom.mem_ker.mp hσ, map_one]
