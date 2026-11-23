import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsJoin
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem SubSystem.twist_sub_eq_mul (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by
  rw [Submodule.mul_eq_span_mul_set]
  change Submodule.span _ _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q, hq, y, hy, rfl⟩
    exact ⟨y, hy, q, hq, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, hy, q, hq, rfl⟩
    exact ⟨q, hq, y, hy, by rw [smul_eq_mul, mul_comm]⟩

theorem twistMod_zero_eq_one (I : Chart x) : twistMod k x 0 I = 1 := by
  obtain ⟨i, hi⟩ := I.2.1
  rw [twistMod_eq_span 0 I hi, zpow_zero, Submodule.one_eq_span]

theorem twistMod_mul_twistMod (a b : ℤ) (I : Chart x) :
    twistMod k x a I * twistMod k x b I = twistMod k x (a + b) I := by
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  rw [twistMod_eq_span a I hi, twistMod_eq_span b I hi, twistMod_eq_span (a + b) I hi,
    Submodule.span_mul_span, Set.singleton_mul_singleton, ← zpow_add₀ hxi]

theorem twistMod_pow_eq (c : ℤ) (n : ℕ) (I : Chart x) :
    twistMod k x c I ^ n = twistMod k x (n * c) I := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, twistMod_zero_eq_one]
  | succ n ih => rw [pow_succ, ih, twistMod_mul_twistMod]; push_cast; ring_nf

theorem SubSystem.pow_sub_eq_pow (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact twistMod_zero_eq_one I
  | succ n ih => rw [pow_succ, ← ih]; exact SubSystem.twist_sub_eq_mul _ _ I

theorem SubSystem.span_secs_le (F : SubSystem k x Ω) (I : Chart x) :
    Submodule.span (chartRing k x I) (F.secs : Set Ω) ≤ F.sub I := by
  rw [Submodule.span_le]
  intro z hz
  exact (Submodule.mem_iInf _).mp hz I

theorem SubSystem.generated_twist {F Q : SubSystem k x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  rw [SubSystem.twist_sub_eq_mul, ← hF I, ← hQ I, Submodule.span_mul_span]
  apply Submodule.span_mono
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun J => ?_
  change a * b ∈ (F.twist Q).sub J
  rw [SubSystem.twist_sub_eq_mul]
  exact Submodule.mul_mem_mul ((Submodule.mem_iInf _).mp ha J) ((Submodule.mem_iInf _).mp hb J)

theorem generated_twistSys_zero : (twistSys k x 0).Generated := by
  intro I
  apply le_antisymm (SubSystem.span_secs_le _ I)
  change twistMod k x 0 I ≤ _
  rw [twistMod_zero_eq_one, Submodule.one_eq_span]
  apply Submodule.span_mono
  rintro _ rfl
  exact (Submodule.mem_iInf _).mpr fun J => one_mem_twistMod_zero J

theorem SubSystem.generated_pow {Q : SubSystem k x Ω} (hQ : Q.Generated) (n : ℕ) :
    (Q.pow n).Generated := by
  induction n with
  | zero => exact generated_twistSys_zero
  | succ n ih => exact SubSystem.generated_twist ih hQ

theorem isUnit_twistMod (c : ℤ) (I : Chart x) : IsUnit (twistMod k x c I) :=
  IsUnit.of_mul_eq_one (twistMod k x (-c) I) (by
    rw [twistMod_mul_twistMod, add_neg_cancel, twistMod_zero_eq_one])

theorem LineBundle.isUnit_sub (Q : LineBundle k x) (I : Chart x) : IsUnit (Q.sub I) := by
  obtain ⟨Q', h⟩ := Q.invertible I
  exact IsUnit.of_mul_eq_one _ h

theorem twist_pow_eq_twistMul_twist (M H T : SubSystem k x Ω)
    (hT : ∀ I, T.sub I = twistMod k x (-1) I) (q c m : ℕ) :
    (M.pow q).twist (H.pow (c * m)) =
      (twistMul M q (m : ℤ)).twist ((T.twist (H.pow c)).pow m) := by
  refine SubSystem.ext_sub fun I => ?_
  simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow, hT]
  change _ = _ * twistMod k x (m : ℤ) I * _
  have key : twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m = 1 := by
    rw [twistMod_pow_eq, twistMod_mul_twistMod, mul_neg_one, add_neg_cancel, twistMod_zero_eq_one]
  calc M.sub I ^ q * H.sub I ^ (c * m)
      = M.sub I ^ q * H.sub I ^ (c * m) * (twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m) := by
        rw [key, mul_one]
    _ = _ := by ring

theorem exists_isSubvar_primeOf (hx : x ≠ 0) : ∃ d : ℕ, IsSubvar x (primeOf (S := k) x) d := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hXi : (X i : Poly k N) ∉ primeOf (S := k) x := by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X]
    exact hi
  have hle : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
  have hpos : ¬ ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≤ 0 := by
    intro h0
    have : Ring.KrullDimLE 0 (Poly k N ⧸ primeOf (S := k) x) := Ring.krullDimLE_iff.mpr (by simpa using h0)
    have hF : IsField (Poly k N ⧸ primeOf (S := k) x) := Ring.KrullDimLE.isField_of_isDomain
    have hne : Ideal.Quotient.mk (primeOf (S := k) x) (X i) ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hmem : X i * g - 1 ∈ primeOf (S := k) x := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hb, map_one, sub_self]
    have h0' := homogeneousComponent_mem_primeOf x hmem 0
    have hc : coeff 0 (X i * g - 1 : Poly k N) = -1 := by
      rw [← congrFun constantCoeff_eq]
      simp
    rw [homogeneousComponent_zero, hc] at h0'
    exact (Ideal.IsPrime.ne_top inferInstance)
      (Ideal.eq_top_of_isUnit_mem _ h0' ((isUnit_one.neg).map (C : k →+* Poly k N)))
  have hbot : ringKrullDim (Poly k N ⧸ primeOf (S := k) x) ≠ ⊥ := fun h => hpos (h ▸ bot_le)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have htop : e ≠ ⊤ := by
    rintro rfl
    rw [← he] at hle
    have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hle
    exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h'))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp htop
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    apply hpos
    rw [← he]
    interval_cases n
    simp
  refine ⟨n - 1, ⟨inferInstance, fun f hf d => homogeneousComponent_mem_primeOf x hf d, le_rfl,
    ⟨i, hXi⟩, ?_⟩⟩
  rw [← he, Nat.sub_add_cancel hn1]
  rfl

theorem isVeryAmple_of_eq_zero (hx : x = 0) (F : SubSystem k x Ω) : IsVeryAmple F := by
  have hI : IsEmpty (Chart x) := ⟨fun I => by
    obtain ⟨i, hi⟩ := I.2.1
    exact (mem_support x).mp (I.2.2 hi) (by rw [hx]; rfl)⟩
  exact ⟨0, fun _ => 0, ⟨fun _ => zero_mem _, fun I => (hI.false I).elim,
    fun _ h => (h rfl).elim, fun _ h => (h rfl).elim⟩⟩

end Lemmas

theorem NefPlusAmple.proof (hGA : GeneratedAmple.Statement.{u, w})
    (hK : VeryAmpleNefPlusAmple.Statement.{u, w}) (hJ : VeryAmpleTwistGenerated.Statement.{u, w}) :
    NefPlusAmple.Statement.{u, w} := by
  intro k _ Ω _ _ N x M H hH hM ε hε
  by_cases hx : x = 0
  · refine ⟨ε.den, ε.num.toNat, ε.den_pos, ?_, isVeryAmple_of_eq_zero hx _⟩
    rw [Rat.den_mul_eq_num, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_pos.mpr hε).le]
  obtain ⟨d, hd⟩ := exists_isSubvar_primeOf (k := k) hx
  obtain ⟨c₀, hc₀⟩ := hGA k Ω N x H hH (twistBundle k x (-1))
  have hc : 1 ≤ max c₀ 1 := le_max_right _ _
  have hgen := hc₀ (max c₀ 1) (le_max_left _ _)
  have hcq : (0 : ℚ) < (max c₀ 1 : ℕ) := by exact_mod_cast hc
  obtain ⟨q, m, hq, hm, hVA⟩ := hK k d Ω N x M hd hM (ε / (max c₀ 1 : ℕ)) (div_pos hε hcq)
  have hm0 : 0 ≤ m := by
    have : (0 : ℚ) ≤ m := by rw [hm]; positivity
    exact_mod_cast this
  have hmq : ((m.toNat : ℕ) : ℚ) = m := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  refine ⟨q, max c₀ 1 * m.toNat, hq, ?_, ?_⟩
  · rw [Nat.cast_mul, hmq, hm]
    field_simp
  · rw [twist_pow_eq_twistMul_twist M.toSubSystem H.toSubSystem (twistBundle k x (-1)).toSubSystem
      (fun _ => rfl)]
    refine hJ k Ω N x _ _ (fun I => ?_) (fun I => ?_) ?_ (SubSystem.generated_pow hgen _)
    · refine IsUnit.exists_right_inv ?_
      simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((M.isUnit_sub I).pow q).mul (isUnit_twistMod _ I)
    · refine IsUnit.exists_right_inv ?_
      simp only [SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((isUnit_twistMod (-1) I).mul ((H.isUnit_sub I).pow _)).pow _
    · rwa [Int.toNat_of_nonneg hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman
