import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSqStatement
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_integral_primitive_clearing : ∀ (K : Type) [Field K] [NumberField K], ∃ θ : K, IsIntegral ℤ θ ∧ 0 < (minpoly ℤ θ).natDegree ∧ ((minpoly ℤ θ).map (Int.castRingHom ℚ)).Separable ∧ ∀ s : K, ∃ N : ℕ, 0 < N ∧ (N : K) * s ∈ Algebra.adjoin ℤ ({θ} : Set K) := by
  intro K _ _
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have halg : IsAlgebraic ℤ α := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  set θ : K := (y : K) * α with hθdef
  have hθ : IsIntegral ℤ θ := by rw [hθdef, ← zsmul_eq_mul]; exact hy
  refine ⟨θ, hθ, minpoly.natDegree_pos hθ, ?_, ?_⟩
  · rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hθ]
    exact Algebra.IsSeparable.isSeparable ℚ θ
  · intro s
    set O := Algebra.adjoin ℤ ({θ} : Set K)
    have hθO : θ ∈ O := Algebra.subset_adjoin rfl
    have hs : s ∈ Algebra.adjoin ℚ ({α} : Set K) := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]
      trivial
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
      rw [hx]
      rcases Int.natAbs_eq y with h | h
      · have : ((y.natAbs : ℕ) : K) = (y : K) := (Int.cast_natCast (R := K) _).symm.trans (congrArg (Int.cast (R := K)) h.symm)
        rw [this]; exact hθO
      · have h' : (y.natAbs : ℤ) = -y := by omega
        have : ((y.natAbs : ℕ) : K) = -(y : K) := (Int.cast_natCast (R := K) _).symm.trans ((congrArg (Int.cast (R := K)) h').trans (Int.cast_neg y))
        rw [this, neg_mul]; exact O.neg_mem hθO
    | algebraMap q =>
      refine ⟨q.den, q.den_pos, ?_⟩
      have : ((q.den : ℕ) : K) * algebraMap ℚ K q = algebraMap ℤ K q.num := by
        rw [algebraMap_int_eq, eq_intCast, ← map_natCast (algebraMap ℚ K), ← map_mul,
          ← map_intCast (algebraMap ℚ K)]
        congr 1
        rw [mul_comm]; exact Rat.mul_den_eq_num q
      rw [this]; exact O.algebraMap_mem _
    | add a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a + b) = (M' : ℤ) • ((M : K) * a) + (M : ℤ) • ((M' : K) * b) := by
        simp only [zsmul_eq_mul]; push_cast; ring
      rw [this]
      exact O.add_mem (O.zsmul_mem hMa _) (O.zsmul_mem hMb _)
    | mul a b _ _ ha hb =>
      obtain ⟨M, hM, hMa⟩ := ha
      obtain ⟨M', hM', hMb⟩ := hb
      refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
      have : ((M * M' : ℕ) : K) * (a * b) = ((M : K) * a) * ((M' : K) * b) := by
        push_cast; ring
      rw [this]
      exact O.mul_mem hMa hMb

theorem nonempty_adjoin_ringHom_zmod_of_dvd_eval : ∀ (K : Type) [Field K] [NumberField K] (θ : K), IsIntegral ℤ θ → ∀ (m : ℕ) (x : ℤ), (m : ℤ) ∣ (minpoly ℤ θ).eval x → Nonempty (Algebra.adjoin ℤ ({θ} : Set K) →+* ZMod m) := by
  intro K _ _ θ hθ m x hx
  have h : Polynomial.eval₂ (Int.castRingHom (ZMod m)) (x : ZMod m) (minpoly ℤ θ) = 0 := by
    rw [Polynomial.eval₂_at_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  exact ⟨(AdjoinRoot.lift (Int.castRingHom (ZMod m)) (x : ZMod m) h).comp (minpoly.equivAdjoin hθ).symm.toRingEquiv.toRingHom⟩

theorem nonempty_closure_ringHom_of_mul_mem : ∀ (K : Type) [Field K] [CharZero K] (O : Subring K) (R : Type) [CommRing R] (ψ : O →+* R) (N : ℕ), 0 < N → IsUnit (N : R) → ∀ (S : Finset K), (∀ s ∈ S, (N : K) * s ∈ O) → Nonempty (Subring.closure (S : Set K) →+* R) := by
  intro K _ _ O R _ ψ N hN hu S hS
  set B := Localization.Away (N : O)
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  have hunits : ∀ m : Submonoid.powers (N : O), IsUnit (O.subtype m) := by
    rintro ⟨m, k, rfl⟩
    simp only [map_pow, map_natCast]
    exact (isUnit_iff_ne_zero.mpr hNK).pow k
  let φ : B →+* K := IsLocalization.lift (M := Submonoid.powers (N : O)) hunits
  have hφa : ∀ a : O, φ (algebraMap O B a) = (a : K) := fun a => IsLocalization.lift_eq hunits a
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (N : O)) b
    have h1 := congrArg φ (IsLocalization.mk'_spec B a m)
    rw [map_mul, hb, zero_mul, hφa] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    subst ha; exact IsLocalization.mk'_zero _
  have hle : Subring.closure (S : Set K) ≤ φ.range := by
    rw [Subring.closure_le]
    intro s hs
    refine ⟨IsLocalization.mk' B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)), ?_⟩
    have h1 := congrArg φ (IsLocalization.mk'_spec B (⟨(N : K) * s, hS s hs⟩ : O) (⟨(N : O), 1, pow_one _⟩ : Submonoid.powers (N : O)))
    rw [map_mul, hφa, hφa] at h1
    simp only [map_natCast] at h1
    exact mul_right_cancel₀ hNK (h1.trans (mul_comm _ _))
  have hψN : IsUnit (ψ (N : O)) := by rw [map_natCast]; exact hu
  let χ : B →+* R := IsLocalization.Away.lift (N : O) hψN
  let e : B ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict ⟨fun x y h => hinj (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  exact ⟨χ.comp (e.symm.toRingHom.comp (Subring.inclusion hle))⟩

theorem exists_prime_sq_ringHom_of_closure : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  intro K _ _ S n
  obtain ⟨θ, hθ, hdeg, hsep, hden⟩ := exists_integral_primitive_clearing K
  choose Nf hNf0 hNf using hden
  set N : ℕ := ∏ s ∈ S, Nf s with hN
  have hN0 : 0 < N := Finset.prod_pos (fun s _ => hNf0 s)
  have hNS : ∀ s ∈ S, (N : K) * s ∈ (Algebra.adjoin ℤ ({θ} : Set K)).toSubring := by
    intro s hs
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem Nf hs
    have : (N : K) * s = (c : ℤ) • ((Nf s : K) * s) := by
      rw [hN, hc]; push_cast; rw [zsmul_eq_mul]; push_cast; ring
    rw [this]
    exact Subalgebra.zsmul_mem _ (hNf s) _
  obtain ⟨p, hp, hlt, x, hx⟩ := GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable (minpoly ℤ θ) hdeg hsep (max n N)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hlt, ?_⟩
  obtain ⟨ψ⟩ := nonempty_adjoin_ringHom_zmod_of_dvd_eval K θ hθ (p ^ 2) x (by exact_mod_cast hx)
  have hu : IsUnit (N : ZMod (p ^ 2)) := by
    rw [ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.not_dvd_of_pos_of_lt hN0 (lt_of_le_of_lt (le_max_right _ _) hlt)
  exact nonempty_closure_ringHom_of_mul_mem K (Algebra.adjoin ℤ ({θ} : Set K)).toSubring (ZMod (p ^ 2)) ψ N hN0 hu S hNS

end GlobalTheory
