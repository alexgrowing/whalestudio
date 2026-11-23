import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem cyc_mem_princ_iff (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (n : ℕ) (g : G F Ω) :
    cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔ ∀ t : Ω, t ^ l ^ n = 1 → g t = t := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have e : cycZ F Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
  have h1 : cycZ F Ω l g ∈ KStar.TotallyRealRoots.princ l n ↔
      (cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow n = 1 := by
    rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, Units.ext_iff, e]
    rfl
  have hpow : ∀ t : Ω, t ^ l ^ n = 1 → t ^ (1 : ZMod (l ^ n)).val = t := by
    intro t ht
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ht, pow_one]
  rw [h1]
  constructor
  · intro h t ht
    have := cyclotomicCharacter.spec l g.toRingEquiv t ht
    rw [h, hpow t ht] at this
    exact this
  · intro h
    rw [cyclotomicCharacter.toZModPow]
    refine (modularCyclotomicCharacter.unique Ω _ _ fun t ht => ?_).symm
    have ht' : (t : Ω) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 ht, Units.val_one]
    rw [hpow _ ht']
    exact h _ ht'

private theorem le_finrank (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ)
    (h : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) : c ≤ Module.finrank ℚ L := by
  have hl : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := h
  have h1 : (l ^ c).totient ≤ Module.finrank ℚ L := by
    rw [← Polynomial.natDegree_cyclotomic (l ^ c) ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ (pow_pos hl.pos c)]
    exact minpoly.natDegree_le ζ
  rcases c with _ | c
  · exact Nat.zero_le _
  · rw [Nat.totient_prime_pow_succ hl] at h1
    have h2 : c < l ^ c := Nat.lt_pow_self hl.one_lt
    have h3 : 1 ≤ l - 1 := by have := hl.two_le; omega
    have h4 : l ^ c * 1 ≤ l ^ c * (l - 1) := Nat.mul_le_mul_left _ h3
    omega

private theorem ex_iff (L : Type) [Field L] [NumberField L] (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L := by
  have hl : l.Prime := Fact.out
  have hb : BddAbove {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)} := ⟨_, fun c hc => le_finrank L l c hc⟩
  refine ⟨fun h => le_csSup hb h, fun h => ?_⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : L, IsPrimitiveRoot ζ (l ^ cZero l L) :=
    Nat.sSup_mem (s := {c : ℕ | ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)}) ⟨0, 1, by simp⟩ hb
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  exact ⟨ζ ^ l ^ d, hζ.pow (pow_pos hl.pos _) (by rw [hd, pow_add, mul_comm])⟩

private theorem all_iff (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l : ℕ) [Fact l.Prime] (c : ℕ) :
    (∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l c) ↔ ∃ ζ : L, IsPrimitiveRoot ζ (l ^ c) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : IsGalois L Ω := IsGalois.mk
  constructor
  · intro h
    obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ c)
    obtain ⟨ζ, rfl⟩ : ξ ∈ Set.range (algebraMap L Ω) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed ξ).2 fun g =>
        (cyc_mem_princ_iff L Ω l c g).1 (h g) ξ hξ.pow_eq_one
    exact ⟨ζ, hξ.of_map_of_injective (algebraMap L Ω).injective⟩
  · rintro ⟨ζ, hζ⟩ g
    have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ c) := hζ.map_of_injective (algebraMap L Ω).injective
    refine (cyc_mem_princ_iff L Ω l c g).2 fun t ht => ?_
    obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one ht
    rw [map_pow, g.commutes]

theorem UpperTheory.V.Tower.muQ :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], (∀ c : ℕ, (∃ ζ : L, IsPrimitiveRoot ζ (l ^ c)) ↔ c ≤ cZero l L) ∧ (∀ c : ℕ, Un L Ω l c = ⊤ ↔ c ≤ cZero l L) ∧
        (HasMuQ l L ↔ qExp l ≤ cZero l L) ∧ (HasMuQ l L → IsTotallyComplex L ∧ Procyc L Ω l) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L) := by
  intro L Ω _ _ _ _ _ l _
  have hl : l.Prime := Fact.out
  have hq : (if l = 2 then 4 else l) = l ^ qExp l := by
    unfold qExp
    split_ifs with h
    · subst h; rfl
    · rw [pow_one]
  have hP : Procyc L Ω l ↔ l ≠ 2 ∨ HasMuQ l L := by
    by_cases h : l = 2
    · have h2 : qExp l = 2 := if_pos h
      rw [Procyc, HasMuQ, hq, h2, ← all_iff L Ω l 2]
      rfl
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  refine ⟨ex_iff L l, fun c => ?_, ?_, fun h => ⟨?_, hP.2 (Or.inr h)⟩, hP⟩
  · rw [← ex_iff, ← all_iff L Ω, Subgroup.eq_top_iff']
    exact forall_congr' fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  · rw [HasMuQ, hq, ex_iff]
  · obtain ⟨ζ, hζ⟩ := h
    refine nrRealPlaces_eq_zero_iff.1 (NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt ?_ hζ)
    have := hl.two_le
    split_ifs <;> omega
