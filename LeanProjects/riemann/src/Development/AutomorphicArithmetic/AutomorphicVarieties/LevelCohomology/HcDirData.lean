import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.EtaKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcPrimProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXiSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Th1Facts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

private theorem sq_neg_one {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) :
    χ ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
  have h : ((-1 : ℤ) : ZMod N) ^ 2 = 1 := by
    push_cast
    exact neg_one_sq
  first
    | rw [← map_pow, h, map_one]
    | rw [sq, ← χ.map_mul, ← sq, h, χ.map_one]

private theorem pow_app {O : Type} [CommRing O] {N : ℕ} (χ : DirichletCharacter O N) (k : ℕ) (a : ℤ)
    (ha : IsCoprime a (N : ℤ)) : (χ ^ k) (a : ZMod N) = χ a ^ k := by
  obtain ⟨u, v, huv⟩ := ha
  have h := congrArg (fun x : ℤ => (x : ZMod N)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at h
  rw [← show ((⟨_, _, (mul_comm _ _).trans h, h⟩ : (ZMod N)ˣ) : ZMod N) = ((a : ℤ) : ZMod N) from rfl]
  exact MulChar.pow_apply_coe χ k _

theorem UpperTheory.V.X.dirData :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ → ∀ q : ℕ, UnitaryThreeInertia.XData l ψ q → ∀ ω : DirichletCharacter c.O l, ω ^ (l - 1) = 1 → ∃ (d f n : ℕ) (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ ∧ f * 2 ^ n ∣ l * N * N ∧ ∀ a : ℤ, IsCoprime a (l * N * N : ℕ) → prodX φ ξ a = (ω a ^ e * psi2 ψ a * th1 l ψ a) ^ 2 * ((ZMod.χ₄ a : ℤ) : c.O) := by
  intro l hl c N iN e ψ o₁ hD q hX ω hω
  have hl2 : l ≠ 2 := hD.l_odd
  have h4l : 4 ≤ c2 ψ := hD.four_le
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨hq0, hq, hb⟩ := hX
  obtain ⟨-, -, hcod, hf0, hfour, hth, hl1⟩ := UpperTheory.V.X.th1Facts c.O N ψ l hl.out hl2
  obtain ⟨-, -, -, h2c, h2N, -⟩ := UpperTheory.V.HV.compCond c.O N ψ 2 Nat.prime_two
  obtain ⟨ξ, hξp, hξ⟩ :=
    UpperTheory.V.X.xiSq c.O two_ne_zero N (psi2 ψ) (c2 ψ) h4l h2c.symm
  obtain ⟨f, φ, hφp, hfd, hφo, hφ⟩ :=
    UpperTheory.V.X.primProd c.O l N ((ω ^ e) ^ 2) (th1 l ψ ^ 2)
  have hdiv : f * 2 ^ (c2 ψ - 1) ∣ l * N * N :=
    mul_dvd_mul (dvd_trans hfd (mul_dvd_mul_left l (DirichletCharacter.conductor_dvd_level _)))
      (dvd_trans (pow_dvd_pow 2 (Nat.sub_le _ 1)) h2N)
  have unitOf : ∀ (m : ℕ) (a : ℤ), IsCoprime a (m : ℤ) → IsUnit ((a : ZMod m)) := by
    rintro m a ⟨u, v, huv⟩
    have h := congrArg (fun x : ℤ => (x : ZMod m)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
      Int.cast_one] at h
    exact ⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩
  refine ⟨f0 l ψ, f, c2 ψ - 1, φ, ξ, ?_, hdiv, ?_⟩
  · have hT : ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      obtain ⟨t, ht⟩ := hl1
      calc ((ω ^ e) ^ 2) ^ (l ^ f0 l ψ - 1) = (ω ^ (l - 1)) ^ (e * 2 * t) := by
            rw [ht, ← pow_mul, ← pow_mul, ← pow_mul]
            congr 1
            ring
        _ = 1 := by rw [hω, one_pow]
    have hT2 : (th1 l ψ ^ 2) ^ (l ^ f0 l ψ - 1) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hth, one_pow]
    refine ⟨hf0, hfour, ?_, hφp, orderOf_dvd_of_pow_eq_one (hφo _ hT hT2), hξp, ?_, ?_⟩
    · exact Odd.of_dvd_nat ((hl.out.odd_of_ne_two hl2).mul hcod) hfd
    · have hfle : f ≤ l * q :=
        Nat.le_of_dvd (Nat.mul_pos hl.out.pos hq0) (dvd_trans hfd (mul_dvd_mul_left l hq))
      have h2 : 2 ^ c2 ψ = 2 * 2 ^ (c2 ψ - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hb' : 2 * (l * q * 4 ^ (l ^ f0 l ψ - 1).factorization 2) ≤ 2 * 2 ^ (c2 ψ - 1) := by
        rw [← mul_assoc, ← h2]
        exact hb
      exact le_trans (Nat.mul_le_mul_right _ hfle) (Nat.le_of_mul_le_mul_left hb' two_pos)
    · have hc1 : IsCoprime (-1 : ℤ) ((l * N : ℕ) : ℤ) := isCoprime_one_left.neg_left
      have hc2 : IsCoprime (-1 : ℤ) (N : ℤ) := isCoprime_one_left.neg_left
      have hm1 : IsCoprime (-1 : ℤ) (l : ℤ) := isCoprime_one_left.neg_left
      have e1 := hφ (-1) hc1
      have e2 := hξ (-1) hc2
      rw [pow_app _ _ _ hm1, pow_app _ _ _ hm1, pow_app _ _ _ hc2] at e1
      have hw : (ω ((-1 : ℤ) : ZMod l) ^ e) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, sq_neg_one, one_pow]
      rw [hw, sq_neg_one, one_mul] at e1
      rw [sq_neg_one, one_mul] at e2
      have h4 : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := by
        first
          | decide
          | rfl
          | simp
      have n1 : (-1 : ZMod f) = ((-1 : ℤ) : ZMod f) := by simp
      have n2 : (-1 : ZMod (2 ^ (c2 ψ - 1))) = ((-1 : ℤ) : ZMod (2 ^ (c2 ψ - 1))) := by simp
      rw [n1, n2, e1, e2, h4]
      simp
  · intro a ha
    have haN : IsCoprime a (N : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_left N (l * N)))
    have halN : IsCoprime a ((l * N : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 (dvd_mul_right (l * N) N))
    have hal : IsCoprime a (l : ℤ) :=
      ha.of_isCoprime_of_dvd_right
        (Int.natCast_dvd_natCast.2 (dvd_trans (dvd_mul_right l N) (dvd_mul_right (l * N) N)))
    have had : IsCoprime a ((f * 2 ^ (c2 ψ - 1) : ℕ) : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hdiv)
    obtain ⟨u, hu⟩ := unitOf _ a had
    rw [UpperTheory.V.X.prodX, MulChar.coeToFun_mul, Pi.mul_apply, ← hu,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
      ZMod.cast_intCast (R := ZMod f) (Dvd.intro _ rfl : f ∣ f * 2 ^ (c2 ψ - 1)) a,
      ZMod.cast_intCast (R := ZMod (2 ^ (c2 ψ - 1)))
        (Dvd.intro_left _ rfl : 2 ^ (c2 ψ - 1) ∣ f * 2 ^ (c2 ψ - 1)) a,
      hφ a halN, hξ a haN, pow_app _ _ _ hal, pow_app _ _ _ hal, pow_app _ _ _ haN]
    ring
