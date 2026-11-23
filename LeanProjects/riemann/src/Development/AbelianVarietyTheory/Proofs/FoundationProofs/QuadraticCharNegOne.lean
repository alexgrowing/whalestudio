import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
open Formalism.FrobeniusOrbits

namespace GlobalTheory.NormSign

theorem descent {d q : ℕ} [Fact d.Prime] (hq : q.Prime) (hne : q ≠ d) {u : ℤ}
    (hu : ¬ IsSquare (-(u : ZMod d))) :
    ∀ (n : ℕ) (C X Y : ℤ), C.natAbs = n → C ^ 2 * u + X ^ 2 = q * d * Y ^ 2 → C = 0 := by
  have hd : d.Prime := Fact.out
  have hdZ : Prime (d : ℤ) := Nat.prime_iff_prime_int.mp hd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C X Y hn h
    by_contra hC
    have hz : (C : ZMod d) ^ 2 * u + (X : ZMod d) ^ 2 = 0 := by
      have := congrArg (Int.cast : ℤ → ZMod d) h
      push_cast at this
      simpa using this
    have hC0 : (C : ZMod d) = 0 := by
      by_contra h0
      apply hu
      refine ⟨X / C, ?_⟩
      field_simp
      linear_combination -hz
    have hX0 : (X : ZMod d) = 0 := by
      rw [hC0] at hz
      simpa using hz
    obtain ⟨C', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd C d).1 hC0
    obtain ⟨X', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd X d).1 hX0
    have hd0 : (d : ℤ) ≠ 0 := hdZ.ne_zero
    have h2 : (d : ℤ) * (C' ^ 2 * u + X' ^ 2) = q * Y ^ 2 := by
      apply mul_left_cancel₀ hd0
      linear_combination h
    have hY : (d : ℤ) ∣ Y := by
      rcases hdZ.dvd_or_dvd (Dvd.intro _ h2) with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hq).1 (Int.natCast_dvd_natCast.1 h3)).symm hne
      · exact hdZ.dvd_of_dvd_pow h3
    obtain ⟨Y', rfl⟩ := hY
    have hC' : C' ≠ 0 := fun h0 => hC (by simp [h0])
    refine hC' (ih C'.natAbs ?_ C' X' Y' rfl ?_)
    · rw [← hn, Int.natAbs_mul, Int.natAbs_natCast]
      have := hd.two_le
      have := Int.natAbs_pos.2 hC'
      nlinarith
    · apply mul_left_cancel₀ hd0
      linear_combination h2

def EvenSq (d : ℕ) [Fact d.Prime] (m : ℕ) : Prop :=
  ∃ k u : ℕ, m = d ^ (2 * k) * u ∧ quadraticChar (ZMod d) u = 1

theorem EvenSq.mul {d : ℕ} [Fact d.Prime] {m n : ℕ} (hm : EvenSq d m) (hn : EvenSq d n) :
    EvenSq d (m * n) := by
  obtain ⟨k, u, rfl, hu⟩ := hm
  obtain ⟨l, v, rfl, hv⟩ := hn
  refine ⟨k + l, u * v, by ring, ?_⟩
  push_cast
  rw [map_mul, hu, hv, one_mul]

theorem quadraticChar_neg_one' {d : ℕ} [Fact d.Prime] (hd : d % 4 = 3) :
    quadraticChar (ZMod d) (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_neg_one_iff]
  simpa using hd

theorem card_sq {l : ℕ} [Fact l.Prime] (hl : l % 4 = 3) {F : Type} [Field F] [Fintype F]
    (h2 : ringChar F ≠ 2) (hF : ringChar F ≠ l) {b : F} (hb : b ^ 2 = -(l : F)) :
    quadraticChar (ZMod l) (Fintype.card F) = 1 := by
  have hl2 : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h := quadraticChar_card_card hl2 (F' := F) h2 (by rwa [ZMod.ringChar_zmod_n])
  rw [h, quadraticChar_neg_one' hl, ZMod.card]
  have hl0 : (l : F) ≠ 0 := by
    intro h0
    have := (ringChar.spec F l).1 h0
    exact hF ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F (ringChar F)) Fact.out).1 this)
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hl0
    linear_combination hb
  have : (((-1 : ℤ) : F) * (l : F)) = b ^ 2 := by rw [hb]; push_cast; ring
  rw [this]
  exact quadraticChar_sq_one' hb0

theorem evenSq_card {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {F : Type} [Field F] [Fintype F]
    {a b : F} (ha : a ^ 2 = -(q : F)) (hb : b ^ 2 = -(d : F)) : EvenSq d (Fintype.card F) := by
  obtain ⟨hq, hd, hq8, hd16, hj⟩ := h
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨f, hp, hf⟩ := FiniteField.card F (ringChar F)
  by_cases h2 : ringChar F = 2
  · refine ⟨0, Fintype.card F, by simp, ?_⟩
    rw [hf, h2]
    push_cast
    have : quadraticChar (ZMod d) 2 = 1 := by
      rw [quadraticChar_one_iff_isSquare, ZMod.exists_sq_eq_two_iff (by omega)]
      · omega
      · exact Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; omega)
    rw [map_pow, this, one_pow]
  by_cases hF : ringChar F = d
  · have h1 := card_sq (l := q) (by omega) h2 (by omega) ha
    rw [hf, hF] at h1
    push_cast at h1
    rw [map_pow] at h1
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym] at hj
    push_cast at hj
    rw [← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)] at hj
    have h3 : quadraticChar (ZMod q) d = -1 := by linarith
    rw [h3, neg_one_pow_eq_one_iff_even (by norm_num)] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, 1, ?_, by simp⟩
    rw [hf, hF, hk, two_mul, mul_one]
  · exact ⟨0, Fintype.card F, by simp, card_sq (by omega) h2 hF hb⟩

theorem evenSq_absNorm {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {E : Type} [Field E] [NumberField E]
    {a b : E} (ha : a ^ 2 = -(q : E)) (hb : b ^ 2 = -(d : E)) (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    EvenSq d (Ideal.absNorm B) := by
  have hint : ∀ (l : ℕ) (x : E), x ^ 2 = -(l : E) → ∃ y : 𝓞 E, y ^ 2 = -(l : 𝓞 E) := by
    intro l x hx
    have : IsIntegral ℤ x := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hx]
      exact (isIntegral_natCast l).neg
    obtain ⟨y, rfl⟩ : ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = x := ⟨⟨x, this⟩, rfl⟩
    refine ⟨y, RingOfIntegers.coe_injective ?_⟩
    rw [map_pow, map_neg, map_natCast]
    exact hx
  obtain ⟨a', ha'⟩ := hint _ _ ha
  obtain ⟨b', hb'⟩ := hint _ _ hb
  induction B using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hB
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]
    exact ⟨0, 1, by simp, by simp⟩
  | h₃ I P hI hP ih =>
    rw [map_mul]
    refine EvenSq.mul ?_ (ih hI)
    haveI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    letI : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
    haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP.ne_zero
    letI : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    refine evenSq_card h (a := Ideal.Quotient.mk P a') (b := Ideal.Quotient.mk P b') ?_ ?_
    · rw [← map_pow, ha']; simp
    · rw [← map_pow, hb']; simp

theorem no_rat {q d : ℕ} [Fact d.Prime] (h : HostHyp q d) {m : ℕ} (hm : EvenSq d m) (A W : ℚ) :
    W ^ 2 ≠ q * d * (A ^ 2 + 4 * m) := by
  obtain ⟨hq, hd, hq8, hd16, -⟩ := h
  obtain ⟨k, u, rfl, hu⟩ := hm
  intro hW
  have hns : ¬ IsSquare (-((u : ℤ) : ZMod d)) := by
    rw [← quadraticChar_neg_one_iff_not_isSquare, ← neg_one_mul, map_mul, quadraticChar_neg_one' (by omega)]
    push_cast
    rw [hu]; norm_num
  have key := descent hq (by omega) hns _ (2 * q * d * d ^ k * A.den * W.den) (q * d * A.num * W.den)
    (W.num * A.den) rfl (by
      apply Int.cast_injective (α := ℚ)
      push_cast
      rw [← Rat.mul_den_eq_num A, ← Rat.mul_den_eq_num W]
      push_cast at hW
      linear_combination (-(q * d * A.den ^ 2 * W.den ^ 2 : ℚ)) * hW)
  have h1 := hq.pos
  have h2 := hd.pos
  have h3 := A.den_pos
  have h4 := W.den_pos
  have : (0 : ℤ) < 2 * q * d * d ^ k * A.den * W.den := by positivity
  omega

theorem absNorm_smul {E : Type} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (B : Ideal (𝓞 E)) :
    Ideal.absNorm (c • B) = Ideal.absNorm B := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv B (c • B) (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm

noncomputable def part {R : Ranks} (H : Host R) (t : H.E) (u : G0) : H.E :=
  ∏ h : R.MA, H.sigmaOf (u, h) t

theorem sigmaOf_mul' {R : Ranks} (H : Host R) (g g' : R.GG) (x : H.E) :
    H.sigmaOf (g * g') x = H.sigmaOf g (H.sigmaOf g' x) := by
  have : H.sigmaOf (g * g') = H.sigmaOf g * H.sigmaOf g' := map_mul (H.gal).symm g g'
  rw [this]; rfl

theorem sigmaOf_part {R : Ranks} (H : Host R) (t : H.E) (g : R.GG) (u : G0) :
    H.sigmaOf g (part H t u) = part H t (g.1 * u) := by
  unfold part
  rw [map_prod]
  refine Fintype.prod_equiv (Equiv.mulLeft g.2) _ _ fun h => ?_
  rw [← sigmaOf_mul']
  rfl

theorem part_neg {R : Ranks} (H : Host R) {t : H.E} (ht : H.conj t = t) (u v : ℤˣ) :
    part H t (u, v) = part H t (-u, -v) := by
  unfold part
  refine Finset.prod_congr rfl fun h _ => ?_
  have h1 : ((-u, -v), h) = (((u, v), h) * R.cc : R.GG) := by
    simp [Formalism.HC.Frame.cc, c0]
  rw [h1, sigmaOf_mul']
  exact congrArg _ ht.symm

theorem exists_rat {R : Ranks} (H : Host R) {x : H.E} (hx : ∀ g, H.sigmaOf g x = x) :
    ∃ r : ℚ, (r : H.E) = x := by
  haveI := H.hostE_isGalois
  obtain ⟨r, hr⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) x).2 fun f => by
    have := hx (H.gal f)
    rwa [Host.sigmaOf, MulEquiv.symm_apply_apply] at this
  exact ⟨r, by simpa using hr⟩

theorem sigmaOf_aE {R : Ranks} (H : Host R) (g : R.GG) :
    H.sigmaOf g (H.sqq) = ((g.1.1 : ℤ) : H.E) * H.sqq := by
  have h := H.gal_sqq (H.sigmaOf g)
  have hg : H.gal (H.sigmaOf g) = g := (H.gal).apply_symm_apply g
  rw [hg] at h
  exact h

theorem sigmaOf_bE {R : Ranks} (H : Host R) (g : R.GG) :
    H.sigmaOf g (H.sqd) = ((g.1.2 : ℤ) : H.E) * H.sqd := by
  have h := H.gal_sqd (H.sigmaOf g)
  have hg : H.gal (H.sigmaOf g) = g := (H.gal).apply_symm_apply g
  rw [hg] at h
  exact h

theorem prod_units {M : Type} [CommMonoid M] (f : ℤˣ → M) : ∏ u, f u = f 1 * f (-1) := by
  rw [UnitsInt.univ, Finset.prod_pair (by decide)]

theorem prod_embT (D : D7) (t : D.host.E) :
    ∏ τ, embT D τ t = D.host.φ₀ (part D.host t (1, 1) * part D.host t (-1, 1)) := by
  let e : ℤˣ × D.R.MA ≃ D.R.Psi :=
    { toFun := fun p => ⟨((p.1, 1), p.2), (Formalism.HC.Frame.mem_Psi_iff _).2 rfl⟩
      invFun := fun g => (g.1.1.1, g.1.2)
      left_inv := fun _ => rfl
      right_inv := fun g => Subtype.ext (Prod.ext (Prod.ext rfl ((Formalism.HC.Frame.mem_Psi_iff _).1 g.2).symm) rfl) }
  rw [← prod_units (fun u => part D.host t (u, 1))]
  unfold part
  rw [← Fintype.prod_prod_type' (fun (u : ℤˣ) (h : D.R.MA) => D.host.sigmaOf ((u, 1), h) t), map_prod]
  symm
  refine Fintype.prod_equiv (e.trans D.eTau.symm) _ _ fun p => ?_
  simp only [embT, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

theorem norm_eq {R : Ranks} (H : Host R) {t : H.E} (ht : H.conj t = t) :
    ((Algebra.norm ℚ t : ℚ) : H.E) = (part H t (1, 1) * part H t (-1, 1)) ^ 2 := by
  haveI := H.hostE_isGalois
  have h := Algebra.norm_eq_prod_automorphisms ℚ t
  rw [← Fintype.prod_equiv (H.gal).symm.toEquiv (fun g => H.sigmaOf g t) _ (fun _ => rfl),
    Fintype.prod_prod_type, Fintype.prod_prod_type, prod_units, prod_units, prod_units] at h
  change _ = part H t (1, 1) * part H t (1, -1) * (part H t (-1, 1) * part H t (-1, -1)) at h
  rw [part_neg H ht 1 (-1), part_neg H ht (-1) (-1), neg_neg] at h
  simp only [eq_ratCast] at h
  rw [h]; ring

theorem part_pos {R : Ranks} (H : Host R) (t : 𝓞 H.E) (B : Ideal (𝓞 H.E)) (ht0 : t ≠ 0)
    (ht : H.conj (t : H.E) = t) (hB : Ideal.span {t} = B * (H.conj • B)) :
    0 < (H.φ₀ (part H (t : H.E) (1, 1) * part H (t : H.E) (-1, 1))).re := by
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  have ha : H.sqq ^ 2 = -(H.q : H.E) := H.sqq_sq
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact ht0 (by simpa using hB)
  have hm := evenSq_absNorm H.hyp ha hb B hB0
  have hm0 : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  set s := part H (t : H.E) (1, 1) with hs
  set s' := part H (t : H.E) (-1, 1) with hs'
  have e1 : part H (t : H.E) (-1, -1) = s := by rw [part_neg H ht]; simp [hs]
  have e2 : part H (t : H.E) (1, -1) = s' := by rw [part_neg H ht]; simp [hs']
  have key : ∀ g : R.GG, (g.1.1 * g.1.2 = 1 ∧ H.sigmaOf g s = s ∧ H.sigmaOf g s' = s') ∨
      (g.1.1 * g.1.2 = -1 ∧ H.sigmaOf g s = s' ∧ H.sigmaOf g s' = s) := by
    rintro ⟨⟨u, v⟩, h⟩
    rw [hs, hs', sigmaOf_part, sigmaOf_part]
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [e1, e2, ← hs, ← hs']
  obtain ⟨n, hn⟩ := exists_rat H (x := s * s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_mul, h1, h2]
    ring
  obtain ⟨A, hA⟩ := exists_rat H (x := s + s') fun g => by
    rcases key g with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> rw [map_add, h1, h2]
    ring
  obtain ⟨W, hW⟩ := exists_rat H (x := (s - s') * (H.sqq * H.sqd)) fun g => by
    rw [map_mul, map_mul, map_sub, sigmaOf_aE, sigmaOf_bE, mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul]
    rcases key g with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> push_cast <;> ring
  have hWn : W ^ 2 = H.q * H.d * (A ^ 2 - 4 * n) := by
    apply Rat.cast_injective (α := H.E)
    push_cast
    rw [hW, hA, hn, mul_pow, mul_pow, ha, hb]
    ring
  have hn2 : n ^ 2 = (Ideal.absNorm B : ℚ) ^ 2 := by
    have h1 : Algebra.norm ℚ (t : H.E) = n ^ 2 := by
      apply Rat.cast_injective (α := H.E)
      rw [norm_eq H ht]
      push_cast
      rw [hn]
    have h2 := congrArg Ideal.absNorm hB
    rw [map_mul, absNorm_smul, Ideal.absNorm_span_singleton] at h2
    have h3 := congrArg (fun k : ℕ => ((k : ℤ) : ℚ)) h2
    simp only [Int.natCast_natAbs] at h3
    push_cast at h3
    rw [Algebra.coe_norm_int, h1, abs_of_nonneg (sq_nonneg _)] at h3
    rw [h3]; ring
  rw [← hn, map_ratCast, Complex.ratCast_re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hn2 with h | h
  · rw [h]; exact_mod_cast hm0
  · exact absurd (by rw [hWn, h]; ring) (no_rat H.hyp hm A W)

theorem norm_pos : ∀ (D : D7) (t : 𝓞 D.host.E) (B : Ideal (𝓞 D.host.E)), t ≠ 0 → D.host.conj (t : D.host.E) = t →
    Ideal.span {t} = B * (D.host.conj • B) → 0 < (∏ τ, embT D τ (t : D.host.E)).re := by
  intro D t B h0 ht hB
  rw [prod_embT]
  exact part_pos D.host t B h0 ht hB

end GlobalTheory.NormSign
