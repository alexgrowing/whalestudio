import Mathlib

open NumberField IsDedekindDomain

namespace ChowFormHeightComparison₂.RegularPointExistence

theorem mem_of_forall_valuationSubring {R F : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field F]
    [Algebra R F] [IsFractionRing R F] {x : F}
    (h : ∀ O : ValuationSubring F, (∀ r : R, algebraMap R F r ∈ O) → x ∈ O) : ∃ a : R, algebraMap R F a = x := by
  by_contra hx
  let S : Subring F := (algebraMap R F).range
  have hxS : x ∉ S := fun hm => hx hm
  letI : Algebra R S := (algebraMap R F).rangeRestrict.toAlgebra
  haveI : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral R S :=
    ⟨fun y => RingHom.isIntegral_of_surjective _ (algebraMap R F).rangeRestrict_surjective y⟩
  haveI : IsIntegrallyClosedIn S F := isIntegrallyClosedIn_iff.2 ⟨Subtype.val_injective, fun {y} hy => by
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (isIntegral_trans (R := R) y hy)
    exact ⟨⟨y, a, ha⟩, rfl⟩⟩
  obtain ⟨V, hV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hxS
  exact hxV (h V fun r => hV ⟨r, rfl⟩)

theorem exists_refine {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (O : ValuationSubring Ω)
    (hO : ∀ a : 𝓞 K, algebraMap K Ω (a : K) ∈ O) :
    ∃ (la : HeightOneSpectrum (𝓞 K)) (O' : ValuationSubring Ω), O' ≤ O ∧
      (∀ a : 𝓞 K, O'.valuation (algebraMap K Ω (a : K)) ≤ 1) ∧
      ∀ a ∈ la.asIdeal, O'.valuation (algebraMap K Ω (a : K)) < 1 := by
  let ι : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K)
  have hι : ∀ a, O.valuation (ι a) ≤ 1 := fun a => (O.valuation_le_one_iff _).2 (hO a)
  let P : Ideal (𝓞 K) :=
    { carrier := {a | O.valuation (ι a) < 1}
      add_mem' := fun {a b} ha hb => by
        show O.valuation (ι (a + b)) < 1
        rw [map_add]
        exact O.valuation.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show O.valuation (ι (c * x)) < 1
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hι c)) hx }
  have hP : P ≠ ⊤ := fun h => by
    have h0 : (1 : 𝓞 K) ∈ P := h ▸ Submodule.mem_top
    have h1 : O.valuation (ι 1) < 1 := h0
    simp at h1
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP
  let la : HeightOneSpectrum (𝓞 K) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩
  have hle : ∀ (x : Ω) (a : 𝓞 K), O.valuation (x - ι a) < 1 → O.valuation x ≤ 1 := fun x a h => by
    have : x = (x - ι a) + ι a := by ring
    rw [this]
    exact O.valuation.map_add_le h.le (hι a)
  have hmul : ∀ (x y : Ω) (a b : 𝓞 K), O.valuation (x - ι a) < 1 → O.valuation (y - ι b) < 1 →
      O.valuation (x * y - ι (a * b)) < 1 := fun x y a b ha hb => by
    have : x * y - ι (a * b) = x * (y - ι b) + ι b * (x - ι a) := by rw [map_mul]; ring
    rw [this]
    refine O.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle x a ha)) hb
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (hι b)) ha
  have hadd : ∀ (x y : Ω) (a b : 𝓞 K), O.valuation (x - ι a) < 1 → O.valuation (y - ι b) < 1 →
      O.valuation (x + y - ι (a + b)) < 1 := fun x y a b ha hb => by
    have : x + y - ι (a + b) = (x - ι a) + (y - ι b) := by rw [map_add]; ring
    rw [this]
    exact O.valuation.map_add_lt ha hb
  let R : Subring Ω :=
    { carrier := {x | ∃ a : 𝓞 K, O.valuation (x - ι a) < 1}
      mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, hmul _ _ a b ha hb⟩
      one_mem' := ⟨1, by simp⟩
      add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, hadd _ _ a b ha hb⟩
      zero_mem' := ⟨0, by simp⟩
      neg_mem' := fun {x} ⟨a, ha⟩ => ⟨-a, by
        have : -x - ι (-a) = -(x - ι a) := by rw [map_neg]; ring
        rw [this, Valuation.map_neg]
        exact ha⟩ }
  let I : Ideal R :=
    { carrier := {x | ∃ a ∈ M, O.valuation ((x : Ω) - ι a) < 1}
      add_mem' := fun ⟨a, ha', ha⟩ ⟨b, hb', hb⟩ => ⟨a + b, M.add_mem ha' hb', hadd _ _ a b ha hb⟩
      zero_mem' := ⟨0, M.zero_mem, by simp⟩
      smul_mem' := fun c x ⟨b, hb', hb⟩ => by
        obtain ⟨a, ha⟩ := c.2
        exact ⟨a * b, M.mul_mem_left a hb', hmul _ _ a b ha hb⟩ }
  have hI : I ≠ ⊤ := fun h => by
    have h0 : (1 : R) ∈ I := h ▸ Submodule.mem_top
    obtain ⟨a, ha', ha⟩ := h0
    have h1 : 1 - a ∈ P := by
      show O.valuation (ι (1 - a)) < 1
      rw [map_sub, map_one]
      exact ha
    have h2 : (1 : 𝓞 K) ∈ M := by simpa using M.add_mem (hPM h1) ha'
    exact hM.ne_top ((Ideal.eq_top_iff_one M).2 h2)
  obtain ⟨B, hRB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hιR : ∀ a, ι a ∈ R := fun a => ⟨a, by simp⟩
  refine ⟨la, B, ValuationSubring.nonunits_le_nonunits.1 fun x hx => ?_, fun a => ?_, fun a ha => ?_⟩
  · have hx' : O.valuation (x - ι 0) < 1 := by
      simpa using (O.mem_nonunits_iff).1 hx
    exact hIB ⟨⟨x, 0, hx'⟩, ⟨0, M.zero_mem, hx'⟩, rfl⟩
  · exact (B.valuation_le_one_iff _).2 (hRB (hιR a))
  · exact (B.mem_nonunits_iff).1 (hIB ⟨⟨ι a, hιR a⟩, ⟨a, ha, by simp⟩, rfl⟩)

end ChowFormHeightComparison₂.RegularPointExistence
