import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.DerivExt

open TrivSqZeroExt

variable {K : Type} [Field K]

def Good (p : ℕ) (f : K) (R : Subring (TrivSqZeroExt K K)) : Prop :=
  (∀ r ∈ R, r.fst = 0 → r = 0) ∧ (∀ g : K, inl (g ^ p) ∈ R) ∧
    (∀ r ∈ R, r.fst ≠ 0 → ∃ t ∈ R, r * t = 1) ∧ (inl f + inr 1 : TrivSqZeroExt K K) ∈ R

lemma inj_of {R : Subring (TrivSqZeroExt K K)} (h0 : ∀ r ∈ R, r.fst = 0 → r = 0)
    {r t : TrivSqZeroExt K K} (hr : r ∈ R) (ht : t ∈ R) (h : r.fst = t.fst) : r = t := by
  have := h0 (r - t) (R.sub_mem hr ht) (by simp [h])
  exact sub_eq_zero.mp this

def fieldOf (R : Subring (TrivSqZeroExt K K))
    (hinv : ∀ r ∈ R, r.fst ≠ 0 → ∃ t ∈ R, r * t = 1) : Subfield K where
  carrier := {x | ∃ r ∈ R, r.fst = x}
  mul_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨r * t, R.mul_mem hr ht, by simp⟩
  one_mem' := ⟨1, R.one_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨r, hr, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨r + t, R.add_mem hr ht, by simp⟩
  zero_mem' := ⟨0, R.zero_mem, by simp⟩
  neg_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨-r, R.neg_mem hr, by simp⟩
  inv_mem' := by
    rintro _ ⟨r, hr, rfl⟩
    by_cases h : r.fst = 0
    · exact ⟨0, R.zero_mem, by simp [h]⟩
    · obtain ⟨t, ht, hrt⟩ := hinv r hr h
      refine ⟨t, ht, ?_⟩
      have := congrArg TrivSqZeroExt.fst hrt
      simp only [fst_mul, fst_one] at this
      exact (eq_inv_of_mul_eq_one_right this)

noncomputable def sec (R : Subring (TrivSqZeroExt K K)) (h0 : ∀ r ∈ R, r.fst = 0 → r = 0)
    (hinv : ∀ r ∈ R, r.fst ≠ 0 → ∃ t ∈ R, r * t = 1) :
    fieldOf R hinv →+* TrivSqZeroExt K K where
  toFun a := Classical.choose a.2
  map_one' := by
    have h := Classical.choose_spec (show ((1 : fieldOf R hinv) : K) ∈ fieldOf R hinv from
      (1 : fieldOf R hinv).2)
    exact inj_of h0 h.1 R.one_mem (by simpa using h.2)
  map_mul' a b := by
    have ha := Classical.choose_spec a.2
    have hb := Classical.choose_spec b.2
    have hab := Classical.choose_spec (a * b).2
    exact inj_of h0 hab.1 (R.mul_mem ha.1 hb.1) (by rw [hab.2, fst_mul, ha.2, hb.2]; rfl)
  map_zero' := by
    have h := Classical.choose_spec (show ((0 : fieldOf R hinv) : K) ∈ fieldOf R hinv from
      (0 : fieldOf R hinv).2)
    exact inj_of h0 h.1 R.zero_mem (by simpa using h.2)
  map_add' a b := by
    have ha := Classical.choose_spec a.2
    have hb := Classical.choose_spec b.2
    have hab := Classical.choose_spec (a + b).2
    exact inj_of h0 hab.1 (R.add_mem ha.1 hb.1) (by rw [hab.2, fst_add, ha.2, hb.2]; rfl)

lemma sec_spec (R : Subring (TrivSqZeroExt K K)) (h0 : ∀ r ∈ R, r.fst = 0 → r = 0)
    (hinv : ∀ r ∈ R, r.fst ≠ 0 → ∃ t ∈ R, r * t = 1) (a : fieldOf R hinv) :
    sec R h0 hinv a ∈ R ∧ (sec R h0 hinv a).fst = a :=
  Classical.choose_spec a.2

lemma good_sSup (p : ℕ) (f : K) (c : Set (Subring (TrivSqZeroExt K K)))
    (hc : c ⊆ {R | Good p f R}) (hch : IsChain (· ≤ ·) c) (y : Subring (TrivSqZeroExt K K))
    (hy : y ∈ c) : Good p f (sSup c) ∧ ∀ z ∈ c, z ≤ sSup c := by
  have hne : c.Nonempty := ⟨y, hy⟩
  have hdir : DirectedOn (· ≤ ·) c := hch.directedOn
  have mem : ∀ x, x ∈ sSup c ↔ ∃ s ∈ c, x ∈ s := fun x => Subring.mem_sSup_of_directedOn hne hdir
  have le : ∀ z ∈ c, z ≤ sSup c := fun z hz => le_sSup hz
  refine ⟨⟨?_, ?_, ?_, ?_⟩, le⟩
  · intro r hr h
    obtain ⟨s, hs, hrs⟩ := (mem r).1 hr
    exact (show Good p f s from hc hs).1 r hrs h
  · intro g
    exact le y hy ((show Good p f y from hc hy).2.1 g)
  · intro r hr h
    obtain ⟨s, hs, hrs⟩ := (mem r).1 hr
    obtain ⟨t, ht, hrt⟩ := (show Good p f s from hc hs).2.2.1 r hrs h
    exact ⟨t, le s hs ht, hrt⟩
  · exact le y hy (show Good p f y from hc hy).2.2.2

private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal (p : ℕ) [Fact p.Prime] [CharP K p] (L : Subfield K)
    (s : L →+* TrivSqZeroExt K K) (hfst : ∀ a : L, (s a).fst = a) (x v : K) (hx : x ∉ L)
    (hxp : x ^ p ∈ L) (hs : s ⟨x ^ p, hxp⟩ = inl (x ^ p)) :
    ∃ R : Subring (TrivSqZeroExt K K), (∀ r ∈ R, r.fst = 0 → r = 0) ∧
      (∀ r ∈ R, r.fst ≠ 0 → ∃ t ∈ R, r * t = 1) ∧ (∀ a : L, s a ∈ R) ∧
      (inl x + inr v : TrivSqZeroExt K K) ∈ R := by
  classical
  have hp : p.Prime := Fact.out
  let c : L := ⟨x ^ p, hxp⟩
  let φ : Polynomial L →+* TrivSqZeroExt K K := Polynomial.eval₂RingHom s (inl x + inr v)
  let ev : Polynomial L →+* K := Polynomial.eval₂RingHom L.subtype x
  have hfstφ : ∀ P : Polynomial L, (φ P).fst = ev P := by
    intro P
    induction P using Polynomial.induction_on with
    | C a => simp [φ, ev, hfst]
    | add P Q hP hQ => simp only [map_add, fst_add, hP, hQ]
    | monomial n a _ =>
      simp [φ, ev, hfst, fst_pow]
  have hpow : (inl x + inr v : TrivSqZeroExt K K) ^ p = inl (x ^ p) := by
    ext
    · simp [fst_pow]
    · simp [snd_pow, CharP.cast_eq_zero K p]
  let m : Polynomial L := Polynomial.X ^ p - Polynomial.C c
  have hφm : φ m = 0 := by
    simp only [m, map_sub, map_pow, φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    rw [hpow]
    simp only [c, hs, sub_self]
  have hevm : ev m = 0 := by
    simp [m, ev, c]
  have hirr : Irreducible m := by
    refine X_pow_sub_C_irreducible_of_prime hp (fun b hb => hx ?_)
    have hb' : (b : K) ^ p = x ^ p := by
      have := congrArg Subtype.val hb
      simpa [c] using this
    have : (b : K) = x := frobenius_inj K p (by simpa [frobenius_def] using hb')
    exact this ▸ b.2
  have hdvd : ∀ P : Polynomial L, ev P = 0 → m ∣ P := by
    intro P hP
    by_contra h
    obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 h
    have := congrArg ev hab
    simp [map_add, map_mul, hevm, hP] at this
  refine ⟨φ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨P, rfl⟩ h
    obtain ⟨Q, rfl⟩ := hdvd P (by rw [← hfstφ]; exact h)
    rw [map_mul, hφm, zero_mul]
  · rintro _ ⟨P, rfl⟩ h
    have hnd : ¬ m ∣ P := by
      rintro ⟨Q, rfl⟩
      exact h (by rw [hfstφ, map_mul, hevm, zero_mul])
    obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hnd
    refine ⟨φ b, ⟨b, rfl⟩, ?_⟩
    have := congrArg φ hab
    rw [map_add, map_mul, map_mul, hφm, mul_zero, zero_add, map_one] at this
    rw [mul_comm]; exact this
  · intro a
    exact ⟨Polynomial.C a, by simp [φ]⟩
  · exact ⟨Polynomial.X, by simp [φ]⟩

lemma exists_good (p : ℕ) [Fact p.Prime] [CharP K p] (f : K) (hf : ∀ g : K, f ≠ g ^ p) :
    ∃ R, Good p f R := by
  have hp : p.Prime := Fact.out
  let L : Subfield K := (frobenius K p).fieldRange
  let s : L →+* TrivSqZeroExt K K := (TrivSqZeroExt.inlHom K K).comp L.subtype
  have hx : f ∉ L := by
    rintro ⟨g, hg⟩
    exact hf g (by rw [← hg, frobenius_def])
  have hxp : f ^ p ∈ L := ⟨f, by simp [frobenius_def]⟩
  obtain ⟨R, h0, hinv, hsR, hfR⟩ := exists_inclusion_mul_eq_mul_inclusion_of_normal p L s (fun a => rfl) f 1 hx hxp rfl
  refine ⟨R, h0, fun g => ?_, hinv, hfR⟩
  exact hsR ⟨g ^ p, ⟨g, by simp [frobenius_def]⟩⟩

theorem exists_derivation (p : ℕ) [Fact p.Prime] [CharP K p] (f : K)
    (hf : ∀ g : K, f ≠ g ^ p) : ∃ D : Derivation ℤ K K, D f = 1 := by
  obtain ⟨R0, hR0⟩ := exists_good p f hf
  obtain ⟨M, -, hM⟩ := zorn_le_nonempty₀ {R | Good p f R}
    (fun c hc hch y hy => ⟨sSup c, (good_sSup p f c hc hch y hy).1, (good_sSup p f c hc hch y hy).2⟩)
    R0 hR0
  obtain ⟨h0, hpw, hinv, hf1⟩ := (show Good p f M from hM.1)
  have hall : ∀ a : K, a ∈ fieldOf M hinv := by
    intro x
    by_contra hx
    have hxp : x ^ p ∈ fieldOf M hinv := ⟨inl (x ^ p), hpw x, by simp⟩
    have hs : sec M h0 hinv ⟨x ^ p, hxp⟩ = inl (x ^ p) :=
      inj_of h0 (sec_spec M h0 hinv _).1 (hpw x) (by rw [(sec_spec M h0 hinv _).2]; simp)
    obtain ⟨R', h0', hinv', hsR', hxR'⟩ := exists_inclusion_mul_eq_mul_inclusion_of_normal p (fieldOf M hinv) (sec M h0 hinv)
      (fun a => (sec_spec M h0 hinv a).2) x 0 hx hxp hs
    have hle : M ≤ R' := by
      intro r hr
      have hmem : r.fst ∈ fieldOf M hinv := ⟨r, hr, rfl⟩
      have := inj_of h0 hr (sec_spec M h0 hinv ⟨r.fst, hmem⟩).1
        (by rw [(sec_spec M h0 hinv _).2])
      rw [this]
      exact hsR' _
    have hgood : Good p f R' := ⟨h0', fun g => hle (hpw g), hinv', hle hf1⟩
    have hR'M := hM.2 hgood hle
    exact hx ⟨_, hR'M hxR', by simp⟩
  let e : K →+* fieldOf M hinv :=
    { toFun := fun a => ⟨a, hall a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let s' : K →+* TrivSqZeroExt K K := (sec M h0 hinv).comp e
  have hs'fst : ∀ a, (s' a).fst = a := fun a => (sec_spec M h0 hinv (e a)).2
  have hs'mem : ∀ a, s' a ∈ M := fun a => (sec_spec M h0 hinv (e a)).1
  let Dl : K →ₗ[ℤ] K :=
    { toFun := fun a => (s' a).snd
      map_add' := fun a b => by simp
      map_smul' := fun n a => by simp }
  refine ⟨Derivation.mk' Dl (fun a b => ?_), ?_⟩
  · simp [Dl, snd_mul, hs'fst, smul_eq_mul]
    ring
  · have : s' f = inl f + inr 1 := inj_of h0 (hs'mem f) hf1 (by simp [hs'fst])
    simp [Dl, this]

end GlobalTheory.DerivExt
