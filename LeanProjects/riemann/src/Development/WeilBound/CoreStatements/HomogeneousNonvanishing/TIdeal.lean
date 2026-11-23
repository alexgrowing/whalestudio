import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem t_ideal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω Ω' : Type) [Field Ω] [CharZero Ω] [Field Ω'] [CharZero Ω'] (φ : Ω →+* Ω') (y : (Σ k, ι k) → Ω), mCoordIdeal (fun p => φ (y p)) = mCoordIdeal y ∧ (blockFnField (fun p => φ (y p))).toSubfield = (blockFnField y).toSubfield.map φ ∧ (Function.Surjective φ → Birational y → Birational (fun p => φ (y p))) ∧ ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
  intro K _ ι _ Ω Ω' _ _ _ _ φ y
  have key : ∀ (s : MRing ι), aeval (fun p => φ (y p)) s = φ (aeval y s) := by
    intro s
    have h := MvPolynomial.comp_aeval_apply (R := ℤ) y (φ.toIntAlgHom) s
    simpa using h.symm
  have cone : ∀ (s : MRing ι), mConeMap (fun p => φ (y p)) s = MvPolynomial.map φ (mConeMap y s) := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p n hp => rw [map_mul, map_mul, hp, map_mul]; simp [mConeMap]
  refine ⟨?_, ?_, ?_, key⟩
  · ext s
    simp only [mCoordIdeal, RingHom.mem_ker]
    rw [cone]
    constructor
    · intro hs
      apply MvPolynomial.map_injective φ φ.injective
      rw [hs, map_zero]
    · intro hs
      rw [hs, map_zero]
  · have e := IntermediateField.adjoin_map ℚ {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q} (φ.toRatAlgHom)
    have e2 := congrArg IntermediateField.toSubfield e
    rw [IntermediateField.toSubfield_map] at e2
    have hs : (φ.toRatAlgHom) '' {t : Ω | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = y p / y q}
        = {t : Ω' | ∃ (p : (k : K) × ι k) (q : (k : K) × ι k), p.fst = q.fst ∧ t = φ (y p) / φ (y q)} := by
      ext t
      constructor
      · rintro ⟨u, ⟨p, q, hpq, rfl⟩, rfl⟩
        exact ⟨p, q, hpq, by simp [map_div₀]⟩
      · rintro ⟨p, q, hpq, rfl⟩
        exact ⟨y p / y q, ⟨p, q, hpq, rfl⟩, by simp [map_div₀]⟩
    rw [hs] at e2
    unfold blockFnField
    exact e2.symm
  · intro hsurj hb s'
    obtain ⟨s, rfl⟩ := hsurj s'
    obtain ⟨d, g, h, hg, hh, hne, heq⟩ := hb s
    refine ⟨d, g, h, hg, hh, ?_, ?_⟩
    · rw [key]
      exact fun h0 => hne (φ.injective (by rw [h0, map_zero]))
    · rw [key, key, heq, map_mul]

end PositivityTheory.UnitarySelfGeneration
