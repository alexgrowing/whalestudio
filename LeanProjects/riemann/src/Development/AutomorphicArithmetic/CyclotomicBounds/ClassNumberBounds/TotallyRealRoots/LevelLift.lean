import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelGroupSupLevelInertia

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem unitsMap_unitsMap' {n m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) (a : (ZMod d)ˣ) :
    ZMod.unitsMap hm (ZMod.unitsMap hd a) = ZMod.unitsMap (dvd_trans hm hd) a := by
  rw [← ZMod.unitsMap_comp hm hd]; rfl

private theorem unitsMap_redPow' {j c : ℕ} (h : l ^ j ∣ l ^ c) (u : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redPow l c u) = redPow l j u := by
  have hjc : j ≤ c := (Nat.pow_dvd_pow_iff_le_right (Fact.out : l.Prime).one_lt).1 h
  apply Units.ext
  rw [ZMod.unitsMap_val]
  exact PadicInt.cast_toZModPow j c hjc (u : ℤ_[l])

private theorem crt_units {n m M : ℕ} [NeZero M] (hn : n ∣ M) (hm : m ∣ M)
    (h : (ZMod n)ˣ) (w : (ZMod m)ˣ)
    (hw : ZMod.unitsMap (Nat.gcd_dvd_left n m) h = ZMod.unitsMap (Nat.gcd_dvd_right n m) w) :
    ∃ a : (ZMod M)ˣ, ZMod.unitsMap hn a = h ∧ ZMod.unitsMap hm a = w := by
  have : NeZero n := ⟨fun h0 => NeZero.ne M (by simpa [h0] using hn)⟩
  have : NeZero m := ⟨fun h0 => NeZero.ne M (by simpa [h0] using hm)⟩
  have hc : (h : ZMod n).val ≡ (w : ZMod m).val [MOD Nat.gcd n m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_val]
    exact congrArg Units.val hw
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder' hc
  have e1 : (k : ZMod n) = h := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hk1, ZMod.natCast_zmod_val]
  have e2 : (k : ZMod m) = w := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hk2, ZMod.natCast_zmod_val]
  have c1 : k.Coprime n := (ZMod.isUnit_iff_coprime k n).1 (e1 ▸ h.isUnit)
  have c2 : k.Coprime m := (ZMod.isUnit_iff_coprime k m).1 (e2 ▸ w.isUnit)
  have c3 : k.Coprime (Nat.lcm n m) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul n m) (Nat.Coprime.mul_right c1 c2)
  have hl : Nat.lcm n m ∣ M := Nat.lcm_dvd hn hm
  obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective hl (ZMod.unitOfCoprime k c3)
  refine ⟨a, ?_, ?_⟩
  · rw [← unitsMap_unitsMap' (Nat.dvd_lcm_left n m) hl, ha]
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_left n m), e1]
  · rw [← unitsMap_unitsMap' (Nat.dvd_lcm_right n m) hl, ha]
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast (Nat.dvd_lcm_right n m), e2]

private theorem unitsMap_congr_pow {g j n c : ℕ} (hg : g = l ^ j) (h1 : g ∣ n) (h2 : g ∣ l ^ c)
    (hn : n ≠ 0) (h : (ZMod n)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd n l) h = redPow l (n.factorization l) u) :
    ZMod.unitsMap h1 h = ZMod.unitsMap h2 (redPow l c u) := by
  subst hg
  have hj : l ^ j ∣ l ^ n.factorization l :=
    pow_dvd_pow l (((Fact.out : l.Prime).pow_dvd_iff_le_factorization hn).1 h1)
  rw [unitsMap_redPow', ← unitsMap_redPow' hj, ← hu, unitsMap_unitsMap']

private theorem lift_aux {n c M : ℕ} [NeZero M] (hn : n ∣ M) (hm : l ^ c ∣ M)
    (h : (ZMod n)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd n l) h = redPow l (n.factorization l) u) :
    ∃ a : (ZMod M)ˣ, ZMod.unitsMap hn a = h ∧ ZMod.unitsMap hm a = redPow l c u := by
  have hn0 : n ≠ 0 := fun h0 => NeZero.ne M (by simpa [h0] using hn)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (Nat.gcd_dvd_right n (l ^ c))
  exact crt_units hn hm h _ (unitsMap_congr_pow hj _ _ hn0 h u hu)

theorem exists_lift_level {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) (u : ℤ_[l]ˣ)
    (hu : ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u) (b : ℕ) :
    ∃ a : (ZMod (N * l ^ b))ˣ, ZMod.unitsMap (Nat.dvd_mul_right N (l ^ b)) a = h ∧
      ZMod.unitsMap (Nat.dvd_mul_left (l ^ b) N) a = redPow l b u := by
  have : NeZero (N * l ^ b) :=
    ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)⟩
  exact lift_aux _ _ h u hu

end KStar.TotallyRealRoots
