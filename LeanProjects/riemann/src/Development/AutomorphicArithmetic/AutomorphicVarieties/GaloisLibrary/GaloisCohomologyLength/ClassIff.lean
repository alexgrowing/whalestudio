import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAbelian

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

private theorem ci_pow {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (a : (ZMod M)ˣ) (ζ : Ω) (hζ : ζ ^ m = 1) :
    ζ ^ (a : ZMod M).val = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  rw [ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ci_hen (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (i : ℕ) :
    HasEnoughRootsOfUnity Ω (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  infer_instance

private theorem ci_spec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (ζ : Ω) (hζ : ζ ^ l ^ n = 1) :
    g ζ = ζ ^ ((KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  have hen := ci_hen Ω l
  exact cyclotomicCharacter.spec l g ζ hζ

private theorem ci_red {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (g : Ω ≃+* Ω) (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : Ω, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    w = KStar.TotallyRealRoots.redPow l n (cyclotomicCharacter Ω l g) := by
  have hen := ci_hen Ω l n
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := ci_spec l n g ζ hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1

private theorem ci_eq {Ω : Type} [Field Ω] {x y : Ω} (hy : y ≠ 0) {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hab.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (div_eq_one_iff_eq hy).1 h3

theorem UpperTheory.V.LDataCardLeFinrank.classIff :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (g : Ω ≃+* Ω) (h : (ZMod N)ˣ), (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) ↔
      ((∀ ζ : Ω, ζ ^ ordCompl[l] N = 1 → g ζ = ζ ^ ((ZMod.unitsMap (Nat.ordCompl_dvd N l) h : (ZMod (ordCompl[l] N))ˣ) : ZMod (ordCompl[l] N)).val) ∧
        ZMod.unitsMap (Nat.ordProj_dvd N l) h = KStar.TotallyRealRoots.redPow l (N.factorization l) (cyclotomicCharacter Ω l g)) := by
  intro Ω _ _ _ l _ N _ g h
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l hN).ne'⟩
  have hmul : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  constructor
  · intro H
    refine ⟨fun ζ hζ => ?_, ci_red l _ g _ fun ζ hζ => ?_⟩
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, mul_comm, pow_mul, hζ, one_pow])
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, pow_mul, hζ, one_pow])
  · rintro ⟨H1, H2⟩ ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN] at hζ
      exact zero_ne_one hζ
    have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) :=
      (Nat.coprime_ordCompl hl hN).pow_left _
    have e1 : (ζ ^ ordProj[l] N) ^ ordCompl[l] N = 1 := by rw [← pow_mul, hmul, hζ]
    have e2 : (ζ ^ ordCompl[l] N) ^ ordProj[l] N = 1 := by rw [← pow_mul, mul_comm, hmul, hζ]
    refine ci_eq (pow_ne_zero _ hζ0) hcop ?_ ?_
    · rw [← map_pow, H1 _ e1, ← ci_pow _ h _ e1, ← pow_mul, ← pow_mul, mul_comm]
    · rw [← map_pow, ci_spec l _ g _ e2, ← H2, ← ci_pow _ h _ e2, ← pow_mul, ← pow_mul, mul_comm]
