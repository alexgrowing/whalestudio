import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

private theorem pow_mod_eq_pow_of_pow_eq_one' {F : Type} [Field F] {z : F} {m : ℕ} (h : z ^ m = 1) (k : ℕ) :
    z ^ (k % m) = z ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k m, pow_add, pow_mul, h, one_pow, mul_one]

private theorem rt_add {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) (i j : ZMod m) :
    ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_add, pow_mod_eq_pow_of_pow_eq_one' h.pow_eq_one, pow_add]

private theorem rt_mul {F : Type} [Field F] {z : F} {m : ℕ} (h : z ^ m = 1) (i j : ZMod m) :
    z ^ (i * j).val = (z ^ i.val) ^ j.val := by
  rw [ZMod.val_mul, pow_mod_eq_pow_of_pow_eq_one' h, pow_mul]

private theorem rt_inj {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) {i j : ZMod m}
    (e : ζ ^ i.val = ζ ^ j.val) : i = j := by
  haveI : NeZero m := ⟨hm.ne'⟩
  exact ZMod.val_injective m (h.pow_inj (ZMod.val_lt i) (ZMod.val_lt j) e)

private theorem rt_ex {F : Type} [Field F] {ζ : F} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m) {z : F}
    (hz : z ^ m = 1) : ∃ i : ZMod m, z = ζ ^ i.val := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨k, hk, hk'⟩ := h.eq_pow_of_pow_eq_one hz
  refine ⟨(k : ZMod m), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk, hk']

private theorem cyc_spec {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ζ : Ω} {m : ℕ} (hm : 0 < m) (h : IsPrimitiveRoot ζ m)
    (s : Ω ≃ₐ[ℚ] Ω) : ∀ z : Ω, z ^ m = 1 → s z = z ^ (cyc m s).val := by
  have hsm : (s ζ) ^ m = 1 := by rw [← map_pow, h.pow_eq_one, map_one]
  obtain ⟨k, hk⟩ := rt_ex hm h hsm
  have hex : ∃ y : ZMod m, ∀ z : Ω, z ^ m = 1 → s z = z ^ y.val := by
    refine ⟨k, fun z hz => ?_⟩
    obtain ⟨i, hi⟩ := rt_ex hm h hz
    rw [hi, map_pow, hk, ← pow_mul, ← pow_mul, mul_comm]
  unfold cyc
  exact Classical.epsilon_spec hex

theorem UpperTheory.V.Z.Kato.Sym.lgB :
    UpperTheory.V.Z.Kato.Sym.LgB := by
  intro Ω _ _ _ ε X m hm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hζΩ : IsPrimitiveRoot (eOm ε (1 / (m : ℚ))) m := isPrimitiveRoot_eOm ε hm.ne'
  have hz : IsPrimitiveRoot (zt X m) m :=
    hζΩ.map_of_injective (f := (io X).comp (algebraMap Ω X.K)) (RingHom.injective _)
  have hspec : ∀ a b : Kb X, b ≠ 0 → a ^ m = b ^ m → a = zt X m ^ (lg X m a b).val * b := by
    intro a b hb hab
    have h1 : (a / b) ^ m = 1 := by rw [div_pow, hab, div_self (pow_ne_zero _ hb)]
    obtain ⟨i, hi⟩ := rt_ex hm hz h1
    have hex : ∃ i : ZMod m, a = zt X m ^ i.val * b := ⟨i, by rw [← hi, div_mul_cancel₀ a hb]⟩
    unfold lg
    exact Classical.epsilon_spec hex
  have huniq : ∀ (a b : Kb X) (i : ZMod m), b ≠ 0 → a = zt X m ^ i.val * b → lg X m a b = i := by
    intro a b i hb hai
    have hab : a ^ m = b ^ m := by
      rw [hai, mul_pow, ← pow_mul, mul_comm i.val m, pow_mul, hz.pow_eq_one, one_pow, one_mul]
    have h2 := hspec a b hb hab
    apply rt_inj hm hz
    apply mul_right_cancel₀ hb
    rw [← h2, ← hai]
  have hne : ∀ b c : Kb X, c ≠ 0 → b ^ m = c ^ m → b ≠ 0 := by
    intro b c hc hbc h0
    have : c ^ m ≠ 0 := pow_ne_zero _ hc
    rw [← hbc, h0, zero_pow hm.ne'] at this
    exact this rfl
  refine ⟨hz, hspec, huniq, ?_, ?_, ?_, ?_⟩
  · intro a b c hc hab hbc
    have hb := hne b c hc hbc
    apply huniq a c _ hc
    rw [rt_add hm hz, mul_assoc, ← hspec b c hc hbc, ← hspec a b hb hab]
  · intro a b a' b' hb hb' hab hab'
    apply huniq _ _ _ (mul_ne_zero hb hb')
    rw [rt_add hm hz]
    conv_lhs => rw [hspec a b hb hab, hspec a' b' hb' hab']
    ring
  · intro σ τ s hadm hl a b hb hab
    have hσb : σ b ≠ 0 := (map_ne_zero σ).2 hb
    have hσz : σ (zt X m) = zt X m ^ (cyc m s).val := by
      show σ ((io X) ((algebraMap Ω X.K) (eOm ε (1 / (m : ℚ))))) =
        ((io X) ((algebraMap Ω X.K) (eOm ε (1 / (m : ℚ))))) ^ (cyc m s).val
      rw [hl, hadm.1, cyc_spec hm hζΩ s _ hζΩ.pow_eq_one, map_pow, map_pow]
    apply huniq _ _ _ hσb
    rw [rt_mul hz.pow_eq_one, ← hσz, ← map_pow, ← map_mul, ← hspec a b hb hab]
  · intro s t
    refine ⟨?_, ?_, cyc_spec hm hζΩ s⟩
    · apply rt_inj hm hζΩ
      rw [← cyc_spec hm hζΩ (s * t) _ hζΩ.pow_eq_one, rt_mul hζΩ.pow_eq_one,
        ← cyc_spec hm hζΩ s _ hζΩ.pow_eq_one, ← map_pow, ← cyc_spec hm hζΩ t _ hζΩ.pow_eq_one]
      rfl
    · apply rt_inj hm hζΩ
      rw [← cyc_spec hm hζΩ 1 _ hζΩ.pow_eq_one, AlgEquiv.one_apply, ZMod.val_one_eq_one_mod,
        pow_mod_eq_pow_of_pow_eq_one' hζΩ.pow_eq_one, pow_one]
