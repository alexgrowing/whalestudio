import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pKumTriv :
    UpperTheory.Kd.C7.SKumTriv := by
  intro l _ _ Ω _ _ _ A _ ζ hζ m n hnm u hu h
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
    exact ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
  have hpos : 0 < l ^ n := pow_pos hp.pos n
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq u hpos
  refine ⟨v, hv, fun s hs => ?_⟩
  obtain ⟨w, hw, hsw⟩ := h s hs
  rw [ZMod.val_zero, pow_zero, one_mul] at hsw
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (v / w) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  have hc : cycMod ℚ Ω l m s = 1 := (Subgroup.mem_inf.1 hs).2
  have h2 : s (v / w) = v / w := fix_of_cycMod hnm hc h1
  have e : v = v / w * w := by field_simp
  calc s v = s (v / w * w) := by rw [← e]
    _ = v / w * w := by rw [map_mul, h2, hsw]
    _ = v := e.symm
