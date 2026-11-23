import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem ka_pw {Ω : Type} [Field Ω] {N : ℕ} [NeZero N] {z : Ω} (hz : z ^ N = 1) (a : ℕ) (k : ZMod N)
    (h : (a : ZMod N) = k) : z ^ k.val = z ^ a := by
  rw [← h, ZMod.val_natCast]
  exact (pow_eq_pow_mod a hz).symm

private theorem ka_down {Ω : Type} [Field Ω] {l : ℕ} {ζ : ℕ → Ω} (h : ∀ m, ζ (m + 1) ^ l = ζ m) (n d : ℕ) :
    ζ (n + d) ^ l ^ d = ζ n := by
  induction d with
  | zero => simp
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]

theorem UpperTheory.Kd.C7.pKumAlg :
    UpperTheory.Kd.C7.SKumAlg := by
  intro l hl _ Ω _ _ _ A _ ζ hζ m n _ s _
  have hne : ∀ r : ℕ, NeZero (l ^ r) := fun r => ⟨(pow_pos hl.out.pos r).ne'⟩
  have h1 : ∀ r, ζ r ^ l ^ r = 1 := fun r => (hζ r).1.pow_eq_one
  haveI := hne n
  refine ⟨?_, ?_, ?_⟩
  · rintro u u' k k' ⟨v, rfl, hv⟩ ⟨v', rfl, hv'⟩
    refine ⟨⟨v * v', mul_pow _ _ _, ?_⟩, ⟨v⁻¹, inv_pow _ _, ?_⟩, fun a => ⟨v ^ a, ?_, ?_⟩⟩
    · rw [map_mul, hv, hv', ka_pw (h1 n) (k.val + k'.val) (k + k') (by simp), pow_add]
      ring
    · have e : ζ n ^ (-k).val * ζ n ^ k.val = 1 := by
        rw [← pow_add, ← ka_pw (h1 n) ((-k).val + k.val) 0 (by simp), ZMod.val_zero, pow_zero]
      rw [map_inv₀, hv, mul_inv, eq_inv_of_mul_eq_one_left e]
    · rw [← pow_mul, ← pow_mul, mul_comm]
    · rw [map_pow, hv, ka_pw (h1 n) (k.val * a) (a * k) (by simp [mul_comm]), mul_pow, pow_mul]
  · rintro u k n' hn' - ⟨v, rfl, hv⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn'
    haveI := hne n'
    refine ⟨v ^ l ^ d, by rw [← pow_mul, ← pow_add, add_comm], ?_⟩
    rw [map_pow, hv, ka_pw (h1 n') k.val _ rfl, mul_pow, ← pow_mul, mul_comm k.val, pow_mul,
      ka_down (fun r => (hζ r).2)]
  · rintro u k t ⟨v, hu, hv⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
    have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
    have ht : t (ζ n) = ζ n ^ ((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val :=
      cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω t) (ζ n) (h1 n)
    refine ⟨t v, ?_, ?_⟩
    · rw [← map_pow, hu, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    · rw [← AlgEquiv.mul_apply, inv_mul_cancel_right, AlgEquiv.mul_apply, hv, map_mul, map_pow, ht, ← pow_mul,
        ka_pw (h1 n) (((cycMod ℚ Ω l n t : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val * k.val) _ (by simp)]
