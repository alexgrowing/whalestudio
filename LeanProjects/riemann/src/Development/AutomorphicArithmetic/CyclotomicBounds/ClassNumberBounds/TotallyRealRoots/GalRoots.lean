import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

private theorem gr_enough [CharZero E] (i : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure E) (l ^ i) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  infer_instance

theorem eps_mem_princ_iff [CharZero E] (g : Gal(AlgebraicClosure E/E)) (n : ℕ) :
    eps l E g ∈ princ l n ↔ ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → g ζ = ζ := by
  haveI := fun i => gr_enough (l := l) (E := E) i
  set L := AlgebraicClosure E
  set σ : L ≃+* L := MulSemiringAction.toRingAut Gal(L/E) L g with hσ
  have hσg : ∀ x : L, σ x = g x := fun x => rfl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity L (l ^ n)
  have key : eps l E g ∈ princ l n ↔
      (modularCyclotomicCharacter L hn σ : ZMod (l ^ n)) = 1 := by
    rw [← cyclotomicCharacter.toZModPow]
    simp only [princ, redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
      map_one]
    rfl
  have hpow : ∀ {M : Type _} [Monoid M] (a : M), a ^ l ^ n = 1 →
      a ^ (1 : ZMod (l ^ n)).val = a := by
    intro M _ a ha
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ha, pow_one]
  rw [key]
  constructor
  · intro h ζ hζ
    have := cyclotomicCharacter.spec l σ ζ hζ
    rw [cyclotomicCharacter.toZModPow, h] at this
    rw [← hσg, this, hpow ζ hζ]
  · intro h
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [mem_rootsOfUnity] at ht
    have ht' : (t : L) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    rw [hpow (t : L) ht', hσg, h _ ht']

theorem isClosed_galImage [CharZero E] : IsClosed (galImage l E : Set ℤ_[l]ˣ) := by
  have hc : Continuous (eps l E) :=
    cyclotomicCharacter.continuous l E (AlgebraicClosure E)
  have : (galImage l E : Set ℤ_[l]ˣ) = Set.range (eps l E) := by
    ext x
    simp [galImage]
  rw [this]
  exact (isCompact_range hc).isClosed

end KStar.TotallyRealRoots
