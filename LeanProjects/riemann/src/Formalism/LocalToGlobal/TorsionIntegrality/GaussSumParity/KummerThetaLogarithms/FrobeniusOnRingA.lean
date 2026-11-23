import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RingAFacts

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

variable (l : ℕ) [Fact l.Prime]

def muSub : Submonoid ℂ_[l] where
  carrier := muPrime l
  one_mem' := ⟨1, one_pos, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp h), by simp⟩
  mul_mem' := by
    rintro a b ⟨n, hn, hln, ha⟩ ⟨m, hm, hlm, hb⟩
    refine ⟨n * m, Nat.mul_pos hn hm, fun h => ?_, ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hlm h]
    · rw [mul_pow, pow_mul, ha, one_pow, mul_comm n m, pow_mul, hb, one_pow, one_mul]

def evK (k : ℕ) : MonoidAlgebra ℤ (muSub l) →ₐ[ℤ] ℂ_[l] :=
  MonoidAlgebra.lift ℤ ℂ_[l] (muSub l) ((muSub l).subtype.comp (powMonoidHom k))

lemma evK_of (k : ℕ) (g : muSub l) :
    evK l k (MonoidAlgebra.of ℤ (muSub l) g) = (g : ℂ_[l]) ^ k := by
  simp [evK]

lemma evK_mem (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : evK l k r ∈ ringA l := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    rw [evK_of]
    exact Subring.pow_mem _ (Subring.subset_closure g.2) k
  | add x y hx hy =>
    rw [map_add]
    exact Subring.add_mem _ hx hy
  | smul a x hx =>
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact Subring.mul_mem _ (intCast_mem _ a) hx

lemma eval_pow_coprime {K : Type*} [Field K] [CharZero K] {n k : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (hn : 0 < n) (hcop : Nat.Coprime k n) (P : Polynomial ℤ)
    (h : P.eval₂ (Int.castRingHom K) ζ = 0) : P.eval₂ (Int.castRingHom K) (ζ ^ k) = 0 := by
  have h1 : Polynomial.aeval ζ P = 0 := by
    rw [Polynomial.aeval_def]
    exact h
  have hd : minpoly ℤ ζ ∣ P := minpoly.isIntegrallyClosed_dvd (hζ.isIntegral hn) h1
  rw [hζ.minpoly_eq_pow_coprime hcop] at hd
  obtain ⟨Q, rfl⟩ := hd
  have h2 : Polynomial.aeval (ζ ^ k) (minpoly ℤ (ζ ^ k)) = 0 := minpoly.aeval _ _
  rw [Polynomial.aeval_def] at h2
  rw [Polynomial.eval₂_mul]
  exact mul_eq_zero_of_left h2 _

lemma exists_poly (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ∀ m : ℕ, n ∣ m → 0 < m → ∀ ζ : ℂ_[l], IsPrimitiveRoot ζ m →
      ∃ P : Polynomial ℤ, ∀ k : ℕ, P.eval₂ (Int.castRingHom ℂ_[l]) (ζ ^ k) = evK l k r := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨n, hn, hln, hg⟩ := g.2
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    have hgm : (g : ℂ_[l]) ^ m = 1 := by
      obtain ⟨c, rfl⟩ := hnm
      rw [pow_mul, hg, one_pow]
    have : NeZero m := ⟨hm.ne'⟩
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hgm
    refine ⟨Polynomial.X ^ i, fun k => ?_⟩
    rw [evK_of, ← hi, Polynomial.eval₂_pow, Polynomial.eval₂_X, ← pow_mul, ← pow_mul, mul_comm]
  | add x y hx hy =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    obtain ⟨n', hn', hln', hP'⟩ := hy
    refine ⟨n * n', Nat.mul_pos hn hn', fun h => ?_, fun m hnm hm ζ hζ => ?_⟩
    · rcases (Fact.out : l.Prime).dvd_mul.mp h with h | h
      exacts [hln h, hln' h]
    · obtain ⟨P, hP⟩ := hP m (dvd_trans (dvd_mul_right _ _) hnm) hm ζ hζ
      obtain ⟨P', hP'⟩ := hP' m (dvd_trans (dvd_mul_left _ _) hnm) hm ζ hζ
      exact ⟨P + P', fun k => by rw [Polynomial.eval₂_add, map_add, hP, hP']⟩
  | smul a x hx =>
    obtain ⟨n, hn, hln, hP⟩ := hx
    refine ⟨n, hn, hln, fun m hnm hm ζ hζ => ?_⟩
    obtain ⟨P, hP⟩ := hP m hnm hm ζ hζ
    exact ⟨Polynomial.C a * P, fun k => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hP, zsmul_eq_mul, map_mul, map_intCast, eq_intCast]⟩

lemma evK_ker (r : MonoidAlgebra ℤ (muSub l)) (h : evK l 1 r = 0) : evK l l r = 0 := by
  obtain ⟨n, hn, hln, hP⟩ := exists_poly l r
  have : NeZero n := ⟨hn.ne'⟩
  have : NeZero (n : ℂ_[l]) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] n
  obtain ⟨P, hP⟩ := hP n dvd_rfl hn ζ hζ
  have h1 : P.eval₂ (Int.castRingHom ℂ_[l]) ζ = 0 := by
    have := hP 1
    rw [pow_one] at this
    rw [this, h]
  have hcop : Nat.Coprime l n := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hln
  rw [← hP l]
  exact eval_pow_coprime hζ hn hcop P h1

def evA (k : ℕ) : MonoidAlgebra ℤ (muSub l) →+* ringA l :=
  (evK l k).toRingHom.codRestrict (ringA l) (evK_mem l k)

lemma evA_coe (k : ℕ) (r : MonoidAlgebra ℤ (muSub l)) : ((evA l k r : ringA l) : ℂ_[l]) = evK l k r := rfl

lemma evA_of (k : ℕ) (g : muSub l) :
    evA l k (MonoidAlgebra.of ℤ (muSub l) g) = (⟨g, Subring.subset_closure g.2⟩ : ringA l) ^ k := by
  apply Subtype.ext
  rw [evA_coe, evK_of]
  rfl

lemma evA_surj : Function.Surjective (evA l 1) := by
  have hle : ringA l ≤ (evK l 1).toRingHom.range := by
    refine Subring.closure_le.mpr fun g hg => ?_
    refine ⟨MonoidAlgebra.of ℤ (muSub l) ⟨g, hg⟩, ?_⟩
    change evK l 1 _ = g
    rw [evK_of, pow_one]
  rintro ⟨x, hx⟩
  obtain ⟨r, hr⟩ := hle hx
  exact ⟨r, Subtype.ext hr⟩

lemma evA_ker : RingHom.ker (evA l 1) ≤ RingHom.ker (evA l l) := by
  intro r hr
  rw [RingHom.mem_ker] at hr ⊢
  apply Subtype.ext
  rw [evA_coe]
  exact evK_ker l r (by rw [← evA_coe, hr]; rfl)

lemma int_fermat (a : ℤ) : ∃ c : ℤ, a - a ^ l = (l : ℤ) * c := by
  have : ((a - a ^ l : ℤ) : ZMod l) = 0 := by
    push_cast
    rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

lemma evA_congr (r : MonoidAlgebra ℤ (muSub l)) :
    ∃ y : ringA l, evA l l r - evA l 1 r ^ l = (l : ringA l) * y := by
  induction r using MonoidAlgebra.induction_on with
  | of g =>
    refine ⟨0, ?_⟩
    rw [evA_of, evA_of, pow_one, sub_self, mul_zero]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    obtain ⟨w, hw⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (evA l 1 x) (evA l 1 y)
    refine ⟨u + v - evA l 1 x * evA l 1 y * w, ?_⟩
    rw [map_add, map_add, hw]
    linear_combination hu + hv
  | smul a x hx =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨c, hc⟩ := int_fermat l a
    have hc' : (a : ringA l) - (a : ringA l) ^ l = (l : ringA l) * (c : ringA l) := by
      exact_mod_cast congrArg (Int.cast : ℤ → ringA l) hc
    refine ⟨(a : ringA l) * u + (c : ringA l) * evA l 1 x ^ l, ?_⟩
    rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, mul_pow]
    linear_combination (a : ringA l) * hu + (evA l 1 x ^ l) * hc'

theorem frobenius_on_ring_a : FrobA := by
  intro l _
  refine ⟨(evA l 1).liftOfSurjective (evA_surj l) ⟨evA l l, evA_ker l⟩, fun ζ hζ => ?_, fun x => ?_⟩
  · have h1 : evA l 1 (MonoidAlgebra.of ℤ (muSub l) ⟨ζ, hζ⟩) = ζ := by
      rw [evA_of, pow_one]
    conv_lhs => rw [← h1]
    rw [RingHom.liftOfSurjective_comp_apply]
    change evA l l _ = _
    rw [evA_of]
  · obtain ⟨r, rfl⟩ := evA_surj l x
    rw [RingHom.liftOfSurjective_comp_apply]
    exact evA_congr l r

end Formalism.L2.Th1.D
