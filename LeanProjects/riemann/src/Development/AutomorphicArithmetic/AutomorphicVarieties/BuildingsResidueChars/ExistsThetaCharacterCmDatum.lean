import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af

private theorem exists_nontrivial_l_torsion_character {A C : Type} [Group A] [Finite A] [IsCyclic A] [CommGroup C] {l : ℕ} (hl : l ∣ Nat.card A)
    {z : C} (hz : z ≠ 1) (hzl : z ^ l = 1) : ∃ φ : A →* C, φ ≠ 1 ∧ ∀ a, φ a ^ l = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := A)
  have ho : orderOf z ∣ orderOf g := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    exact (orderOf_dvd_of_pow_eq_one hzl).trans hl
  have e : monoidHomOfForallMemZpowers hg ho g = z := monoidHomOfForallMemZpowers_apply_gen hg ho
  refine ⟨monoidHomOfForallMemZpowers hg ho, fun h => hz (by rw [← e, h, MonoidHom.one_apply]), fun a => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  rw [map_zpow, e, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzl, one_zpow]

theorem UpperTheory.exists_theta_character_cmDatum : UpperTheory.V.Sd.S3.ThetaEx := by
  unfold UpperTheory.V.Sd.S3.ThetaEx
  intro Ω _ _ _ l _ w hw hwl
  unfold KillsMu
  haveI : Fact w.Prime := ⟨hw⟩
  have hlp : Nat.Prime l := Fact.out
  have hdvd : l ∣ Nat.card (ZMod w)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hw]
    exact (Nat.modEq_iff_dvd' hw.one_lt.le).1 hwl.symm
  haveI : IsAlgClosed (Qbar l) := inferInstance
  haveI : NeZero (l : Qbar l) := ⟨by exact_mod_cast hlp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) l
  let z : (Qbar l)ˣ := (hζ.isUnit hlp.ne_zero).unit
  have hz : z ≠ 1 := by
    intro h
    apply hζ.ne_one hlp.one_lt
    simpa [z] using congrArg Units.val h
  have hzl : z ^ l = 1 := by
    ext
    simp [z, hζ.pow_eq_one]
  obtain ⟨φ, hφ, hφl⟩ := exists_nontrivial_l_torsion_character (A := (ZMod w)ˣ) hdvd hz hzl
  refine ⟨φ.comp (UpperTheory.V.Chr.cls ℚ Ω w), ?_, ?_, ?_⟩
  · intro h
    apply hφ
    ext u
    obtain ⟨s, rfl⟩ := (UpperTheory.V.Chr.clsOnto Ω w).1 u
    have := DFunLike.congr_fun h s
    simpa using this
  · ext s
    simp [hφl]
  · intro s hs
    haveI : Fact (1 < w) := ⟨hw.one_lt⟩
    have h1 : UpperTheory.V.Chr.cls ℚ Ω w s = 1 :=
      (UpperTheory.V.Chr.clsFacts ℚ Ω w).2.2.1 s 1 (fun ζ hζ => by
        rw [Units.val_one, ZMod.val_one, pow_one]
        exact hs ζ hζ)
    rw [MonoidHom.comp_apply, h1, map_one]
