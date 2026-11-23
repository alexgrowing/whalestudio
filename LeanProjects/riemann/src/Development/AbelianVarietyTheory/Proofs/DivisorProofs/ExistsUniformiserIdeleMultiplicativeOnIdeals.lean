import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt UniqueFactorizationMonoid

namespace GlobalTheory.CMVal.IdealIdele

variable {E : Type} [Field E] [NumberField E]

open Classical in

def primeIdele (p : Ideal (𝓞 E)) : (Af E)ˣ :=
  if h : p.IsPrime ∧ p ≠ ⊥ then unifAt ⟨p, h.1, h.2⟩ else 1

def idl (I : Ideal (𝓞 E)) : (Af E)ˣ := ((normalizedFactors I).map primeIdele).prod

theorem idl_top : idl (⊤ : Ideal (𝓞 E)) = 1 := by
  rw [idl, ← Ideal.one_eq_top, normalizedFactors_one]; simp

theorem idl_mul {I J : Ideal (𝓞 E)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥) : idl (I * J) = idl I * idl J := by
  rw [idl, normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]; rfl

theorem nf_prime (v : HeightOneSpectrum (𝓞 E)) : normalizedFactors v.asIdeal = {v.asIdeal} := by
  rw [normalizedFactors_irreducible v.irreducible, normalize_eq]

theorem idl_prime (v : HeightOneSpectrum (𝓞 E)) : idl v.asIdeal = unifAt v := by
  rw [idl, nf_prime, Multiset.map_singleton, Multiset.prod_singleton, primeIdele,
    dif_pos ⟨v.isPrime, v.ne_bot⟩]

theorem ind {P : Ideal (𝓞 E) → Prop} (h1 : P ⊤)
    (h2 : ∀ (v : HeightOneSpectrum (𝓞 E)) (I : Ideal (𝓞 E)), I ≠ ⊥ → P I → P (v.asIdeal * I)) :
    ∀ I, I ≠ ⊥ → P I := fun I => by
  refine induction_on_prime (P := fun I => I ≠ ⊥ → P I) I (fun h => absurd rfl h) ?_ ?_
  · intro x hx _
    rw [Ideal.isUnit_iff.1 hx]; exact h1
  · intro a p ha hp h _
    exact h2 ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩ a ha (h ha)

theorem mul_apply' (a b : (Af E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((a * b : (Af E)ˣ) : Af E) w = (a : Af E) w * (b : Af E) w := rfl

theorem one_apply' (w : HeightOneSpectrum (𝓞 E)) : ((1 : (Af E)ˣ) : Af E) w = 1 := rfl

theorem modF_idl : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → modF (idl I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹ := by
  refine ind ?_ ?_
  · rw [idl_top, modF_eq_one fun w => by rw [one_apply', map_one]]
    simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, ObjModel.modF_mul, h, idl_prime, modF_unifAt, map_mul]
    push_cast
    rw [mul_inv]

open Classical in
theorem val_idl (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    Valued.v ((idl I : Af E) w) = WithZero.exp (-((normalizedFactors I).count w.asIdeal : ℤ)) := by
  refine ind ?_ ?_
  · rw [idl_top, one_apply', map_one, ← Ideal.one_eq_top, normalizedFactors_one]; simp
  · intro v I hI h
    rw [idl_mul v.ne_bot hI, mul_apply', map_mul, h, idl_prime, normalizedFactors_mul v.ne_bot hI, nf_prime,
      Multiset.count_add]
    by_cases hw : w = v
    · subst hw
      rw [(unifAt_spec w).2, ← WithZero.exp_add, Multiset.count_singleton_self]
      congr 1; push_cast; ring
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      rw [(unifAt_spec v).1 w hw, map_one, one_mul, Multiset.count_singleton, if_neg this, zero_add]

theorem idl_eq_one (w : HeightOneSpectrum (𝓞 E)) : ∀ I : Ideal (𝓞 E), I ≠ ⊥ →
    ¬ w.asIdeal ∣ I → (idl I : Af E) w = 1 := by
  refine ind ?_ ?_
  · intro _; rw [idl_top, one_apply']
  · intro v I hI h hd
    have hw : w ≠ v := by
      rintro rfl
      exact hd (dvd_mul_right _ _)
    rw [idl_mul v.ne_bot hI, mul_apply', h fun h => hd (h.mul_left _), idl_prime, (unifAt_spec v).1 w hw, one_mul]

theorem mem_nf {w : HeightOneSpectrum (𝓞 E)} {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) (h : w.asIdeal ∣ I) :
    w.asIdeal ∈ normalizedFactors I :=
  (mem_normalizedFactors_iff hI).2 ⟨w.prime, h⟩

open Classical in
theorem exists_count (n : HeightOneSpectrum (𝓞 E) → ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ I : Ideal (𝓞 E), I ≠ ⊥ ∧ ∀ w : HeightOneSpectrum (𝓞 E),
      (normalizedFactors I).count w.asIdeal = if w ∈ S then n w else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun w => by rw [normalizedFactors_one]; simp⟩
  | insert v S hv ih =>
    obtain ⟨I, hI, h⟩ := ih
    have h0 : v.asIdeal ^ n v ≠ 0 := pow_ne_zero _ v.ne_bot
    refine ⟨v.asIdeal ^ n v * I, mul_ne_zero h0 hI, fun w => ?_⟩
    rw [normalizedFactors_mul h0 hI, normalizedFactors_pow, nf_prime, Multiset.count_add, h, Multiset.count_nsmul,
      Multiset.count_singleton]
    by_cases hw : w = v
    · subst hw; simp [hv]
    · have : w.asIdeal ≠ v.asIdeal := fun h => hw (HeightOneSpectrum.ext h)
      simp [this, hw]

theorem finite_val_ne_one (z : (Af E)ˣ) : {w : HeightOneSpectrum (𝓞 E) | Valued.v ((z : Af E) w) ≠ 1}.Finite :=
  GlobalTheory.Mem.TupHecke.finite_nonunit z

theorem main : ∀ (E : Type) [Field E] [NumberField E], ∃ t : Ideal (𝓞 E) → (Af E)ˣ, t ⊤ = 1 ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → t (I * J) = t I * t J) ∧ (∀ v : HeightOneSpectrum (𝓞 E), t v.asIdeal = unifAt v) ∧
    (∀ I, I ≠ ⊥ → modF (t I) = ((Ideal.absNorm I : ℕ) : ℝ)⁻¹) ∧
    (∀ I, I ≠ ⊥ → ∀ w : HeightOneSpectrum (𝓞 E), Valued.v ((t I : Af E) w) ≤ 1 ∧
      (w.asIdeal ∣ I → Valued.v ((t I : Af E) w) < 1) ∧ (¬ w.asIdeal ∣ I → (t I : Af E) w = 1)) ∧
    (∀ I J, I ≠ ⊥ → J ≠ ⊥ → (∀ w, Valued.v ((t I : Af E) w) = Valued.v ((t J : Af E) w)) → I = J) ∧
    ∀ z : (Af E)ˣ, (∀ w, Valued.v ((z : Af E) w) ≤ 1) →
      ∃ I, I ≠ ⊥ ∧ ∀ w, Valued.v ((t I : Af E) w) = Valued.v ((z : Af E) w) := by
  intro E _ _
  classical
  refine ⟨idl, idl_top, fun _ _ => idl_mul, idl_prime, modF_idl, fun I hI w => ⟨?_, fun hd => ?_, idl_eq_one w I hI⟩,
    fun I J hI hJ h => ?_, fun z hz => ?_⟩
  · rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  · have := Multiset.count_pos.2 (mem_nf hI hd)
    rw [val_idl w I hI, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · have e : normalizedFactors I = normalizedFactors J := by
      ext p
      by_cases hp : Prime p
      · have := h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
        rw [val_idl _ I hI, val_idl _ J hJ, WithZero.exp_inj] at this
        simpa using this
      · rw [Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h),
          Multiset.count_eq_zero.2 fun h => hp (prime_of_normalized_factor _ h)]
    rw [← Ideal.prod_normalizedFactors_eq_self hI, e, Ideal.prod_normalizedFactors_eq_self hJ]
  · obtain ⟨I, hI, h⟩ := exists_count (fun w => (-(Valued.v ((z : Af E) w)).log).toNat)
      (finite_val_ne_one z).toFinset
    refine ⟨I, hI, fun w => ?_⟩
    rw [val_idl w I hI, h]
    split_ifs with hw
    · have h0 := ObjModel.coord_ne z w
      have h1 : (Valued.v ((z : Af E) w)).log ≤ 0 := by
        rw [← WithZero.exp_le_exp, WithZero.exp_log h0]; exact hz w
      rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
    · have : Valued.v ((z : Af E) w) = 1 := by simpa using hw
      rw [this]; simp

end GlobalTheory.CMVal.IdealIdele
