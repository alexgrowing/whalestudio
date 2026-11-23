import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 PowerSeries

namespace GlobalTheory.Col

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def KumVal (n : ℕ) (ζ u : Ω) (s : G ℚ Ω) (k : ZMod (l ^ n)) : Prop :=
  ∃ v : Ω, v ^ (l ^ n) = u ∧ s v = ζ ^ k.val * v

def KumPres (A : ValuationSubring Ω) (n r : ℕ) (ζ : Ω) (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι]
    (u : ι → Ω) (o : ι → Qbar l) : Prop :=
  IsPrimitiveRoot ζ (l ^ n) ∧ n ≤ r ∧ (∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) ∧ (∀ i, ‖o i‖ ≤ 1) ∧
    ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → s ζ = ζ →
      ∃ k : ι → ZMod (l ^ n), (∀ i, KumVal n ζ (u i) s (k i)) ∧ Cg n (Z s 1) (∑ i, o i * ((k i).val : Qbar l))

theorem kumVal_unique {n : ℕ} {ζ u : Ω} {s : G ℚ Ω} {k k' : ZMod (l ^ n)} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hs : s ζ = ζ)
    (hu : u ≠ 0) (hk : KumVal n ζ u s k) (hk' : KumVal n ζ u s k') : k = k' := by
  obtain ⟨v, hv, hsv⟩ := hk
  obtain ⟨w, hw, hsw⟩ := hk'
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hu (by rw [← hv, zero_pow hpos.ne'])
  have hw0 : w ≠ 0 := by rintro rfl; exact hu (by rw [← hw, zero_pow hpos.ne'])
  have h1 : (w / v) ^ (l ^ n) = 1 := by rw [div_pow, hv, hw, div_self hu]
  obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
  have hwv : w = ζ ^ j * v := by rw [hj]; field_simp
  have e1 : s w = ζ ^ k.val * w := by
    rw [hwv, map_mul, map_pow, hs, hsv]; ring
  have e2 : ζ ^ k.val = ζ ^ k'.val := by
    have := e1.symm.trans hsw
    exact mul_right_cancel₀ hw0 this
  exact ZMod.val_injective _ (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt k') e2)

theorem kumVal_one (n : ℕ) (ζ : Ω) (s : G ℚ Ω) : KumVal (l := l) n ζ 1 s 0 :=
  ⟨1, one_pow _, by simp⟩

theorem kumPres_empty (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ (l ^ n)) (hnr : n ≤ r)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (hZ : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 → Z s 1 = 0) :
    KumPres A n r ζ Z (ι := Empty) (fun i => i.elim) (fun i => i.elim) := by
  refine ⟨hζ, hnr, fun i => i.elim, fun i => i.elim, fun s hs hc _ => ⟨fun i => i.elim, fun i => i.elim, ?_⟩⟩
  rw [Cg, hZ s hs hc, Finset.sum_eq_zero (fun i _ => i.elim), sub_zero, norm_zero]
  exact norm_nonneg _

example (A : ValuationSubring Ω) {n r : ℕ} {ζ : Ω} (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (o : Unit → Qbar l) :
    ¬ KumPres A n r ζ Z (fun _ : Unit => (0 : Ω)) o :=
  fun h => (h.2.2.1 ()).2.1 rfl

example (A : ValuationSubring Ω) {r : ℕ} (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι] (u : ι → Ω)
    (o : ι → Qbar l) : ¬ KumPres A 1 r (1 : Ω) Z u o := by
  rintro ⟨h, -⟩
  have := h.eq_orderOf
  rw [orderOf_one, pow_one] at this
  exact (Fact.out : l.Prime).one_lt.ne this.symm

theorem fix_of_cycMod [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)] {n r : ℕ} (hnr : n ≤ r) {s : G ℚ Ω}
    (hs : cycMod ℚ Ω l r s = 1) {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t := by
  have ht' : t ^ (l ^ r) = 1 := by
    obtain ⟨d, hd⟩ := pow_dvd_pow l hnr
    rw [hd, pow_mul, ht, one_pow]
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht'
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow r = 1 := by
    have := congrArg Units.val hs
    simpa [cycMod, cycZ] using this
  rw [h2, ZMod.val_one_eq_one_mod] at h1
  have h3 : t ^ (1 % l ^ r) = t := by
    rcases Nat.lt_or_ge 1 (l ^ r) with h | h
    · rw [Nat.mod_eq_of_lt h, pow_one]
    · have e : l ^ r = 1 := le_antisymm h (Nat.one_le_pow _ _ (Fact.out : l.Prime).pos)
      rw [e, Nat.mod_self, pow_zero]
      rw [e, pow_one] at ht'
      exact ht'.symm
  exact h1.trans h3

end GlobalTheory.Col
