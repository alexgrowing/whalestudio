import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitNormOfSelfDualHermitianLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelfDualHermitianLatticeExistsNormOneModStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianLatticeNormOneOfNormOneModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquareStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOneStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OddGenus

theorem two_unit : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem exists_orthonormal_perp : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K), (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → ∀ (W : Submodule K V) (n : ℕ) (e : Fin (n + 1) → V) (z : V), (∀ i, e i ∈ W) → (∀ i j, h (e i) (e j) = if i = j then 1 else 0) → z ∈ W → h z z = 1 → ∃ e' : Fin n → V, (∀ i, e' i ∈ W) ∧ (∀ i j, h (e' i) (e' j) = if i = j then 1 else 0) ∧ ∀ i, h (e' i) z = 0 := by
  intro K V _ _ _ _ σ h hh hdef W n e z he hee hz hzz
  have h00 : h (e 0) (e 0) = 1 := by simpa using hee 0 0
  have hs0 : ∀ i : Fin n, h (e i.succ) (e 0) = 0 := fun i => by simpa using hee i.succ 0
  have hss : ∀ i j : Fin n, h (e i.succ) (e j.succ) = if i = j then 1 else 0 := fun i j => by
    simpa using hee i.succ j.succ
  by_cases hc : h (e 0) z = 1
  · have : z - e 0 = 0 := hdef _ (by
      have h1 : h z (e 0) = 1 := by rw [hh, hc, map_one]
      simp [hzz, h00, hc, h1])
    rw [sub_eq_zero] at this
    subst this
    exact ⟨fun i => e i.succ, fun i => he _, hss, hs0⟩
  · have hc1 : h (e 0) z - 1 ≠ 0 := sub_ne_zero.2 hc
    have hc2 : σ (h (e 0) z) - 1 ≠ 0 := by
      rw [← map_one σ, ← map_sub]; exact (map_ne_zero σ).2 hc1
    have hz0 : h z (e 0) = σ (h (e 0) z) := hh _ _
    have h0s : ∀ i : Fin n, h (e 0) (e i.succ) = 0 := fun i => by rw [hh, hs0, map_zero]
    have hzs : ∀ i : Fin n, h z (e i.succ) = σ (h (e i.succ) z) := fun i => hh _ _
    refine ⟨fun i => e i.succ + (h (e i.succ) z / (h (e 0) z - 1)) • (z - e 0),
      fun i => W.add_mem (he _) (W.smul_mem _ (W.sub_mem hz (he 0))), fun i j => ?_, fun i => ?_⟩
    · simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.sub_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hss, hs0, h0s, hzs, hzz, h00, hz0,
        map_div₀, map_one]
      field_simp
      ring
    · simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.sub_apply, smul_eq_mul, hzz]
      field_simp
      ring

theorem exists_orthogonal : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) [FiniteDimensional K V], (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → ∃ v : Fin (Module.finrank K V) → V, (∀ i, v i ≠ 0) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by
  intro K V _ _ _ _ σ h _ hh hdef
  suffices H : ∀ k, k ≤ Module.finrank K V →
      ∃ v : Fin k → V, (∀ i, v i ≠ 0) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 from H _ le_rfl
  intro k
  induction k with
  | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hv0, hv⟩ := ih (by omega)
    have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi fun i : Fin k => h.flip (v i))
      (by simp; omega)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hxv : ∀ i, h x (v i) = 0 := fun i => congrFun (LinearMap.mem_ker.1 hx) i
    have hvx : ∀ i, h (v i) x = 0 := fun i => by rw [hh, hxv, map_zero]
    refine ⟨Fin.cons x v, fun i => Fin.cases hx0 hv0 i, fun i j => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [hxv]
    · simp [hvx]
    · intro hij
      simpa using hv i j (fun e => hij (by rw [e]))

theorem binary_one_mod : ∀ (p : ℕ) (u v : ℚ), p.Prime → padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1 := by
  intro p u v hp hu hv
  haveI : Fact p.Prime := ⟨hp⟩
  have key : ∀ w : ℚ, padicNorm p w = 1 → ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ padicNorm p (w - n) < 1 := by
    intro w hw
    have h1 : ‖(w : ℚ_[p])‖ = 1 := by rw [Padic.eq_padicNorm, hw]; simp
    obtain ⟨n, hn⟩ := PadicInt.denseRange_intCast.exists_dist_lt (⟨(w : ℚ_[p]), h1.le⟩ : ℤ_[p]) one_pos
    have h2 : padicNorm p (w - n) < 1 := by
      have h3 : ‖((w - n : ℚ) : ℚ_[p])‖ < 1 := by
        have h4 : dist (w : ℚ_[p]) ((n : ℤ_[p]) : ℚ_[p]) < 1 := hn
        rw [dist_eq_norm] at h4
        simpa using h4
      rw [Padic.eq_padicNorm] at h3
      exact_mod_cast h3
    refine ⟨n, fun hd => ?_, h2⟩
    have h4 : padicNorm p (n : ℚ) < 1 := padicNorm.int_lt_one_iff n |>.2 hd
    have h5 := padicNorm.nonarchimedean (p := p) (q := w - n) (r := n)
    rw [sub_add_cancel, hw] at h5
    exact absurd h5 (not_le.2 (max_lt h2 h4))
  obtain ⟨m, hm, hum⟩ := key u hu
  obtain ⟨n, hn, hvn⟩ := key v hv
  have hm' : (m : ZMod p) ≠ 0 := fun h => hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m p).1 h)
  have hn' : (n : ZMod p) ≠ 0 := fun h => hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).1 h)
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod p, (m : ZMod p) * a ^ 2 + (n : ZMod p) * b ^ 2 - 1 = 0 := by
    rcases hp.eq_two_or_odd with rfl | hodd
    · refine ⟨1, 0, ?_⟩
      have h2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := two_unit
      rw [h2 _ hm']; ring
    · obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
        (f := Polynomial.C (m : ZMod p) * Polynomial.X ^ 2)
        (g := Polynomial.C (n : ZMod p) * Polynomial.X ^ 2 - 1)
        (Polynomial.degree_C_mul_X_pow 2 hm')
        (by
          rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_C_mul_X_pow 2 hn']
          · rfl
          · simp)
        (by rw [ZMod.card]; exact hodd)
      refine ⟨a, b, ?_⟩
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_one] at hab
      linear_combination hab
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective b
  refine ⟨a, b, ?_⟩
  have h1 : padicNorm p ((m * a ^ 2 + n * b ^ 2 - 1 : ℤ) : ℚ) < 1 :=
    (padicNorm.int_lt_one_iff _).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by push_cast; exact hab))
  have h2 : ∀ (w : ℚ) (c : ℤ), padicNorm p w < 1 → padicNorm p (w * (c : ℚ) ^ 2) < 1 := by
    intro w c hw
    rw [padicNorm.mul]
    have := padicNorm.of_int (p := p) (c ^ 2)
    push_cast at this
    exact lt_of_le_of_lt (mul_le_of_le_one_right (padicNorm.nonneg _) this) hw
  have e : u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1 =
      ((u - m) * (a : ℚ) ^ 2 + (v - n) * (b : ℚ) ^ 2) + ((m * a ^ 2 + n * b ^ 2 - 1 : ℤ) : ℚ) := by
    push_cast; ring
  rw [e]
  exact lt_of_le_of_lt padicNorm.nonarchimedean (max_lt (lt_of_le_of_lt padicNorm.nonarchimedean
    (max_lt (h2 _ _ hum) (h2 _ _ hvn))) h1)

theorem exists_unit_vector : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1 := GlobalTheory.T.exists_padicNorm_one_of_selfDual_hermitian_lattice

theorem exists_one_mod : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := GlobalTheory.T.selfDual_hermitianLattice_exists_norm_one_mod

theorem exists_norm_one : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∃ e ∈ W, h e e = 1) → (∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1) → ∃ z ∈ L, z ∈ W ∧ h z z = 1 := GlobalTheory.T.hermitianLattice_norm_one_of_norm_one_mod_prime

theorem orthonormal_of_diagonal : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := GlobalTheory.T.exists_orthonormal_hermitian_of_diag_pos_isSquare

theorem exists_local_ring : ∀ (K : Type) [Field K] [CharZero K] (p : ℕ), p.Prime → ∃ O : Subring K, (∀ x : K, x ∈ O ↔ ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : K) * x)) ∧ ∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1 := by
  intro K _ _ p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : ∀ t : ℕ, IsIntegral ℤ (t : K) := fun t => isIntegral_natCast (R := ℤ) t
  refine ⟨{ carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : K) * x)}
            mul_mem' := ?_, one_mem' := ⟨1, by simp, by simpa using isIntegral_one⟩, add_mem' := ?_,
            zero_mem' := ⟨1, by simp, by simpa using isIntegral_zero⟩, neg_mem' := ?_ },
    fun x => Iff.rfl, fun r => ⟨?_, fun hr => ?_⟩⟩
  · rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : K) * (x * y) = (s : K) * x * ((t : K) * y) := by push_cast; ring
    rw [e]; exact hx.mul hy
  · rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, ?_⟩
    have e : ((s * t : ℕ) : K) * (x + y) = (t : K) * ((s : K) * x) + (s : K) * ((t : K) * y) := by
      push_cast; ring
    rw [e]; exact ((hn t).mul hx).add ((hn s).mul hy)
  · rintro x ⟨s, hs, hx⟩
    exact ⟨s, hs, by simpa using hx.neg⟩
  · rintro ⟨s, hs, hx⟩
    have h1 : IsIntegral ℤ ((s : ℚ) * r) := by
      rw [← isIntegral_algebraMap_iff (algebraMap ℚ K).injective]
      simpa using hx
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
    have h2 : padicNorm p (s : ℚ) = 1 :=
      (padicNorm.nat_eq_one_iff s).2 ((Nat.Prime.coprime_iff_not_dvd hp).1 hs.symm)
    have h3 := padicNorm.of_int (p := p) n
    rw [show (n : ℚ) = (s : ℚ) * r from hn', padicNorm.mul, h2, one_mul] at h3
    exact h3
  · refine ⟨r.den, ?_, ?_⟩
    · have h1 : ‖(r : ℚ_[p])‖ ≤ 1 := by rw [Padic.eq_padicNorm]; exact_mod_cast hr
      exact ((Nat.Prime.coprime_iff_not_dvd hp).2 (by
        have h2 := PadicInt.isUnit_iff.1 (PadicInt.isUnit_den r h1)
        intro hd
        have h3 := (PadicInt.norm_natCast_lt_one_iff (p := p)).2 hd
        rw [h2] at h3
        exact lt_irrefl _ h3)).symm
    · have : ((r.den : ℕ) : K) * (r : K) = (r.num : K) := by
        rw [← Rat.cast_natCast, ← Rat.cast_mul, Rat.den_mul_eq_num, Rat.cast_intCast]
      rw [this]; exact isIntegral_algebraMap (R := ℤ) (x := r.num)

theorem host_quadratic : ∀ D : D7, Module.finrank D.host.K D.host.E = fF D ∧ ∃ (σ : D.host.K →+* D.host.K) (θ : D.host.K), (∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) ∧ θ ^ 2 = -(D.host.d : D.host.K) ∧ σ θ = -θ ∧ (∀ x : D.host.K, ∃ a b : ℚ, x = (a : D.host.K) + (b : D.host.K) * θ) ∧ IsIntegral ℤ ((1 + θ) / 2) ∧ (∀ y : D.host.E, D.host.conj (D.host.conj y) = y) ∧ (∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y)) ∧ ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := GlobalTheory.T.imaginary_quadratic_field_structure

theorem mem_iff_entries : ∀ (D : D7) (N N' : ℕ) (x : Matrix (Fin N') (Fin N) D.host.E), x ∈ YYl D (stdL D N) (stdL D N') ↔ ∀ i j, x i j ∈ D.host.AA0 := by
  intro D N N' x
  have hstd : ∀ (n : ℕ) (v : Fin n → D.host.E), v ∈ stdL D n ↔ ∀ i, IsIntegral ℤ (v i) := by
    intro n v
    simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hhom : ∀ A ∈ homL D (stdL D N) (stdL D N'), ∀ i j, IsIntegral ℤ (A i j) := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA =>
      intro i j
      have := (hstd _ _).1 (hA (Pi.single j 1) ((hstd _ _).2 fun k => by
        rw [Pi.single_apply]; split_ifs; exacts [isIntegral_one, isIntegral_zero])) i
      simpa using this
    | zero => intro i j; exact isIntegral_zero
    | add A B _ _ hA hB => intro i j; exact (hA i j).add (hB i j)
    | smul c A _ hA => intro i j; exact c.isIntegral_coe.mul (hA i j)
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨a, ha, A, hA, rfl⟩ := hB
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul, mul_comm]
      exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨_, hhom A hA i j⟩ ha
    | zero => intro i j; exact D.host.AA0.zero_mem
    | add A B _ _ hA hB =>
      intro i j; exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).add_mem (hA i j) (hB i j)
    | smul c A _ hA =>
      intro i j; exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem c (hA i j)
  · intro hx
    rw [Matrix.matrix_eq_sum_single x]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.subset_span
      ⟨x i j, hx i j, Matrix.single i j 1, Submodule.subset_span fun v hv => (hstd _ _).2 fun k => ?_, by simp⟩
    rw [Matrix.single_mulVec, Function.update_apply]
    split_ifs
    · simpa using (hstd _ _).1 hv j
    · exact isIntegral_zero

theorem local_dual : ∀ (D : D7) (p : ℕ) (x : D.host.E), (∀ y ∈ D.host.AA0, ∃ s : ℕ, Nat.Coprime s p ∧ IsIntegral ℤ ((s : D.host.K) * Algebra.trace D.host.K D.host.E (x * D.host.conj y))) → ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * x ∈ D.host.AA0 := by
  intro D p x hx
  have hfg : ((D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).restrictScalars ℤ).FG :=
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA0).restrictScalars
  obtain ⟨S, hS⟩ := hfg
  have hmem : ∀ y : S, (y : D.host.E) ∈ D.host.AA0 := fun y => by
    have : (y : D.host.E) ∈ Submodule.span ℤ (S : Set D.host.E) := Submodule.subset_span y.2
    rw [hS] at this; exact this
  choose s hs hsx using fun y : S => hx y (hmem y)
  refine ⟨∏ y, s y, Nat.Coprime.prod_left fun y _ => hs y, ?_⟩
  refine (factMMUnimodular D.R D.host _).2 fun y hy => ?_
  have hy' : y ∈ Submodule.span ℤ (S : Set D.host.E) := by rw [hS]; exact hy
  suffices H : IsIntegral ℤ (Algebra.trace D.host.K D.host.E
      (((∏ y, s y : ℕ) : D.host.E) * x * D.host.conj y)) from ⟨⟨_, H⟩, rfl⟩
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ ⟨y, hy⟩)
    have h1 := (isIntegral_natCast (R := ℤ) t).mul (hsx ⟨y, hy⟩)
    rw [ht, mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, Nat.cast_mul, mul_comm _ (t : D.host.K), mul_assoc]
    exact h1
  | zero => simpa using isIntegral_zero
  | add y z _ _ hy hz => rw [map_add, mul_add, map_add]; exact hy.add hz
  | smul c y _ hy =>
    rw [map_zsmul, mul_smul_comm, map_zsmul]; exact hy.zsmul c

theorem local_frame : ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ (n : ℕ) (W : Submodule K V) (e : Fin n → V), (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∀ i, e i ∈ W) → (∀ i j, h (e i) (e j) = if i = j then 1 else 0) → ∃ b : Fin n → V, (∀ i, b i ∈ W ∧ b i ∈ L) ∧ ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσ hK hO hω hQ hh hdef hL hLL hb n
  induction n with
  | zero => intro W e _ _ _; exact ⟨e, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W e hW he hee
    have h0 : ∃ e ∈ W, h e e = 1 := ⟨e 0, he 0, by simpa using hee 0 0⟩
    obtain ⟨z, hzL, hzW, hz⟩ := exists_norm_one K V σ h p d θ O L hp hd hθ hσ hK hO hω hQ hh hdef hL hLL hb W h0
      (exists_one_mod K V σ h p d θ O L hp hd hθ hσ hK hO hω hQ hh hdef hL hLL hb
        (fun u v => binary_one_mod p u v hp)
        (exists_unit_vector K V σ h p d θ O L hp hd hθ hσ hK hO hω hQ hh hdef hL hLL hb) W hW h0)
    obtain ⟨e', he', hee', hez⟩ := exists_orthonormal_perp K V σ h hh hdef W n e z he hee hzW hz
    obtain ⟨b, hb1, hb2⟩ := ih (W ⊓ LinearMap.ker (h.flip z)) e' (by
      intro x hx hy
      have hxz : h x z = 0 := hx.2
      refine hW x hx.1 fun y hyL hyW => ?_
      have h1 := hy (y - h y z • z) (L.sub_mem hyL (hL _ (hLL y hyL z hzL) z hzL))
        ⟨W.sub_mem hyW (W.smul_mem _ hzW), by
          change h (y - h y z • z) z = 0
          simp [hz]⟩
      simpa [hxz] using h1) (fun i => ⟨he' i, hez i⟩) hee'
    refine ⟨Fin.cons z b, fun i => ?_, fun i j => ?_⟩
    · refine Fin.cases ⟨hzW, hzL⟩ (fun i => ⟨(hb1 i).1.1, (hb1 i).2⟩) i
    · have hbz : ∀ i, h (b i) z = 0 := fun i => (hb1 i).1.2
      have hzb : ∀ i, h z (b i) = 0 := fun i => by rw [hh, hbz, map_zero]
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simp [hz]
      · simp [hzb, (Fin.succ_ne_zero _).symm]
      · simp [hbz]
      · simp [hb2]

theorem smul_eq (D : D7) (c : D.host.K) (x : D.host.E) : c • x = (c : D.host.E) * x := rfl

theorem exists_form (D : D7) (σ : D.host.K →+* D.host.K)
    (hσ : ∀ x : D.host.K, ((σ x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E)) (N N' : ℕ) :
    ∃ h : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.K] Matrix (Fin N') (Fin N) D.host.E →ₛₗ[σ] D.host.K,
      ∀ x y, h x y = hYY D x y := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id _) σ (hYY D) ?_ ?_ ?_ ?_, fun _ _ => rfl⟩
  · intro x x' y
    simp only [hYY, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add]
  · intro c x y
    simp only [hYY, Matrix.smul_apply, RingHom.id_apply, ← map_smul, Finset.smul_sum, smul_mul_assoc]
  · intro x y y'
    simp only [hYY, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]
  · intro c x y
    simp only [hYY, Matrix.smul_apply, ← map_smul, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq, smul_eq, map_mul, hσ]; ring

theorem hYY_herm (D : D7) (σ : D.host.K →+* D.host.K)
    (hc : ∀ y : D.host.E, D.host.conj (D.host.conj y) = y)
    (ht : ∀ y : D.host.E, Algebra.trace D.host.K D.host.E (D.host.conj y) = σ (Algebra.trace D.host.K D.host.E y))
    {N N' : ℕ} (x y : Matrix (Fin N') (Fin N) D.host.E) : hYY D y x = σ (hYY D x y) := by
  simp only [hYY, ← ht, map_sum D.host.conj, map_mul, hc, mul_comm]

theorem hYY_pos (D : D7)
    (hp : ∀ y : D.host.E, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K))
    {N N' : ℕ} (x : Matrix (Fin N') (Fin N) D.host.E) (hx : x ≠ 0) :
    ∃ a : ℚ, 0 < a ∧ hYY D x x = (a : D.host.K) := by
  have h1 : ∀ y : D.host.E, ∃ a : ℚ, 0 ≤ a ∧ (y ≠ 0 → 0 < a) ∧
      Algebra.trace D.host.K D.host.E (y * D.host.conj y) = (a : D.host.K) := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, le_rfl, fun h => absurd hy h, by simp [hy]⟩
    · obtain ⟨a, ha, h⟩ := hp y hy
      exact ⟨a, ha.le, fun _ => ha, h⟩
  choose a ha0 ha1 ha2 using h1
  obtain ⟨i, j, hij⟩ : ∃ i j, x i j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (Matrix.ext hn)
  refine ⟨∑ i, ∑ j, a (x i j), ?_, ?_⟩
  · refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => ha0 _) ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun j _ => ha0 _) ⟨j, Finset.mem_univ _, ha1 _ hij⟩
  · simp only [hYY, map_sum, ha2, Rat.cast_sum]

theorem hYY_single (D : D7) {N N' : ℕ} (x : Matrix (Fin N') (Fin N) D.host.E) (i : Fin N') (j : Fin N)
    (y : D.host.E) :
    hYY D x (Matrix.single i j y) = Algebra.trace D.host.K D.host.E (x i j * D.host.conj y) := by
  unfold hYY
  congr 1
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Matrix.single_apply, hb.symm]
  · simp
  · intro b _ hb; simp [Matrix.single_apply, hb.symm]
  · simp

theorem exists_orthonormal (D : D7) (N N' : ℕ) (hev : Even (N * N')) :
    ∃ e : Fin (fF D * N * N') → Matrix (Fin N') (Fin N) D.host.E, Orthonormal D e := by
  obtain ⟨hf, σ, θ, hσ, hθ, hσθ, hK, -, hc, ht, hp⟩ := host_quadratic D
  obtain ⟨h₁, hh₁⟩ := exists_form D σ hσ 1 1
  obtain ⟨h, hh⟩ := exists_form D σ hσ N N'
  obtain ⟨w, hw0, hw⟩ := exists_orthogonal D.host.K (Matrix (Fin 1) (Fin 1) D.host.E) σ h₁
    (fun x y => by rw [hh₁, hh₁, hYY_herm D σ hc ht])
    (fun x hx => by
      by_contra h0
      obtain ⟨a, ha, h1⟩ := hYY_pos D hp x h0
      rw [hh₁, h1] at hx
      exact ha.ne' (by exact_mod_cast hx))
  have hr : Module.finrank D.host.K (Matrix (Fin 1) (Fin 1) D.host.E) = fF D := by
    rw [Module.finrank_matrix, hf]; simp
  choose a ha0 ha using fun k => hYY_pos D hp (w k) (hw0 k)
  let ε : (Fin (Module.finrank D.host.K (Matrix (Fin 1) (Fin 1) D.host.E)) × Fin N) × Fin N' ≃
      Fin (fF D * N * N') := Fintype.equivFinOfCardEq (by simp [hr])
  have h11 : ∀ x y : Matrix (Fin 1) (Fin 1) D.host.E,
      hYY D x y = Algebra.trace D.host.K D.host.E (x 0 0 * D.host.conj (y 0 0)) := by
    intro x y; simp [hYY]
  obtain ⟨e, he⟩ := orthonormal_of_diagonal D.host.K _ σ h D.host.d θ D.host.hyp.2.1.pos hθ hσθ hK (fF D * N * N')
    (fun t => Matrix.single (ε.symm t).2 (ε.symm t).1.2 (w (ε.symm t).1.1 0 0))
    (fun t => a (ε.symm t).1.1) (fun t => ha0 _) (by
      intro s t
      obtain ⟨⟨⟨k, j⟩, i⟩, rfl⟩ := ε.surjective s
      obtain ⟨⟨⟨k', j'⟩, i'⟩, rfl⟩ := ε.surjective t
      simp only [hh, hYY_single, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
      by_cases hij : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := hij
        rw [Matrix.single_apply_same, ← h11]
        by_cases hk : k = k'
        · subst hk; simp [ha]
        · rw [← hh₁, hw k k' hk]; simp [hk]
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij, if_neg (by tauto)]; simp)
    (by
      rw [← ε.prod_comp (fun t => a (ε.symm t).1.1)]
      simp only [Equiv.symm_apply_apply, Fintype.prod_prod_type, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, ← pow_mul, Finset.prod_pow]
      have hev' : Even (N' * N) := mul_comm N N' ▸ hev
      first | exact hev.isSquare_pow _ | exact hev'.isSquare_pow _)
  exact ⟨e, fun i j => by rw [← hh]; exact he i j⟩

theorem natCast_mul_mem (D : D7) (t : ℕ) {x : D.host.E} (hx : x ∈ D.host.AA0) :
    (t : D.host.E) * x ∈ D.host.AA0 := by
  have := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_of_tower_mem t hx
  rwa [nsmul_eq_mul] at this

theorem integral_mul_mem (D : D7) {c x : D.host.E} (hc : IsIntegral ℤ c) (hx : x ∈ D.host.AA0) :
    c * x ∈ D.host.AA0 :=
  (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem ⟨c, hc⟩ hx

def locLat (D : D7) (N N' p : ℕ) : AddSubgroup (Matrix (Fin N') (Fin N) D.host.E) where
  carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ ∀ i j, (s : D.host.E) * x i j ∈ D.host.AA0}
  zero_mem' := ⟨1, by simp, fun i j => by
    rw [Matrix.zero_apply, mul_zero]; exact D.host.AA0.zero_mem⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun i j => ?_⟩
    have : _ ∈ D.host.AA0 := (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).add_mem
      (natCast_mul_mem D t (hx i j)) (natCast_mul_mem D s (hy i j))
    convert this using 1
    simp only [Matrix.add_apply]; push_cast; ring
  neg_mem' := by
    rintro x ⟨s, hs, hx⟩
    refine ⟨s, hs, fun i j => ?_⟩
    rw [Matrix.neg_apply, mul_neg]
    exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).neg_mem (hx i j)

theorem mem_locLat_of_entries (D : D7) (N N' p : ℕ) (x : Matrix (Fin N') (Fin N) D.host.E)
    (hx : ∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * x i j ∈ D.host.AA0) :
    x ∈ locLat D N N' p := by
  choose s hs hsx using hx
  refine ⟨∏ t : Fin N' × Fin N, s t.1 t.2, Nat.Coprime.prod_left fun t _ => hs _ _, fun i j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun t : Fin N' × Fin N => s t.1 t.2) (Finset.mem_univ (i, j))
  rw [hc]
  convert natCast_mul_mem D c (hsx i j) using 1
  push_cast; ring

theorem trace_integral (D : D7) {x y : D.host.E} (hx : x ∈ D.host.AA0) (hy : y ∈ D.host.AA0) :
    IsIntegral ℤ (Algebra.trace D.host.K D.host.E (x * D.host.conj y)) := by
  obtain ⟨c, hc⟩ := (factMMUnimodular D.R D.host x).1 hx y hy
  rw [← hc]; exact c.isIntegral_coe

theorem odd_one : ∀ D : D7, odd1 D := by
  intro D N N' hev p hp
  obtain ⟨e, he⟩ := exists_orthonormal D N N' hev
  obtain ⟨hf, σ, θ, hσ, hθ, hσθ, hK, hω, hc, ht, hpos⟩ := host_quadratic D
  obtain ⟨h, hh⟩ := exists_form D σ hσ N N'
  obtain ⟨O, hO, hQ⟩ := exists_local_ring D.host.K p hp
  have hLL : ∀ x ∈ locLat D N N' p, ∀ y ∈ locLat D N N' p, h x y ∈ O := by
    rintro x ⟨s, hs, hx⟩ y ⟨t, ht', hy⟩
    refine (hO _).2 ⟨s * t, Nat.Coprime.mul_left hs ht', ?_⟩
    have e1 : ((s * t : ℕ) : D.host.K) * h x y = ∑ i, ∑ j, Algebra.trace D.host.K D.host.E
        ((s : D.host.E) * x i j * D.host.conj ((t : D.host.E) * y i j)) := by
      rw [hh, hYY, ← smul_eq_mul, ← map_smul]
      simp only [← map_sum, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq, map_mul, map_natCast]; push_cast; ring
    rw [e1]
    exact IsIntegral.sum _ fun i _ => IsIntegral.sum _ fun j _ => trace_integral D (hx i j) (hy i j)
  obtain ⟨b, hb, hbb⟩ := local_frame D.host.K _ σ h p D.host.d θ O (locLat D N N' p) hp D.host.hyp.2.1
    hθ hσθ hK
    (by
      intro x hx
      obtain ⟨s, hs, hx⟩ := (hO x).1 hx
      refine (hO _).2 ⟨s, hs, ?_⟩
      have := hx.map σ.toIntAlgHom
      simpa using this)
    ((hO _).2 ⟨1, by simp, by simpa using hω⟩) hQ
    (fun x y => by rw [hh, hh, hYY_herm D σ hc ht])
    (fun x hx => by
      by_contra h0
      obtain ⟨a, ha, h1⟩ := hYY_pos D hpos x h0
      rw [hh, h1] at hx
      exact ha.ne' (by exact_mod_cast hx))
    (by
      rintro a ha x ⟨t, ht', hx⟩
      obtain ⟨s, hs, ha⟩ := (hO a).1 ha
      refine ⟨s * t, Nat.Coprime.mul_left hs ht', fun i j => ?_⟩
      have h1 : IsIntegral ℤ (((s : D.host.K) * a : D.host.K) : D.host.E) :=
        ha.map (algebraMap D.host.K D.host.E).toIntAlgHom
      convert integral_mul_mem D h1 (hx i j) using 1
      rw [Matrix.smul_apply, smul_eq]; push_cast; ring)
    hLL
    (by
      intro x
      have h1 : ∀ i j, ∃ m : ℕ, ∃ s : ℕ, Nat.Coprime s p ∧
          IsIntegral ℤ ((s : D.host.E) * (p : D.host.E) ^ m * x i j) := by
        intro i j
        obtain ⟨n, y, hn, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
          (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x i j))).exists_nsmul_eq
          (integralClosure ℤ D.host.E)
        obtain ⟨m, s, hs, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
        refine ⟨m, s, ((Nat.Prime.coprime_iff_not_dvd hp).2 hs).symm, ?_⟩
        have h2 : IsIntegral ℤ ((p ^ m * s) • x i j) := hy ▸ y.2
        convert h2 using 1
        rw [nsmul_eq_mul]; push_cast; ring
      choose m hm using h1
      refine ⟨∑ t : Fin N' × Fin N, m t.1 t.2, mem_locLat_of_entries D N N' p _ fun i j => ?_⟩
      obtain ⟨s, hs, hx⟩ := hm i j
      obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum
        (f := fun t : Fin N' × Fin N => m t.1 t.2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j)))
      refine ⟨s, hs, ?_⟩
      convert natCast_mul_mem D (p ^ c) (integral_mul_mem D hx (Formalism.L2.Pj.one_mem_inverse_halfDifferent D)) using 1
      rw [hc', Matrix.smul_apply, smul_eq]; push_cast; ring)
    _ ⊤ e
    (by
      intro x _ hx
      refine mem_locLat_of_entries D N N' p x fun i j => local_dual D p _ fun y hy => ?_
      rw [← hYY_single, ← hh]
      refine (hO _).1 (hx _ ⟨1, by simp, fun a c => ?_⟩ trivial)
      rw [Matrix.single_apply]
      split_ifs
      · simpa using hy
      · rw [mul_zero]; exact D.host.AA0.zero_mem)
    (fun _ => trivial) (fun i j => by rw [hh]; exact he i j)
  have hcoef : ∀ (c : Fin (fF D * N * N') → D.host.K) j, h (∑ i, c i • b i) (b j) = c j := by
    intro c j
    simp [hbb]
  have hli : LinearIndependent D.host.K b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0 j
    rw [← hcoef c j, hc0]; simp
  have hsp : Submodule.span D.host.K (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by
      rw [Module.finrank_matrix, hf]; simp; ring)
  refine ⟨b, ⟨fun i j => by rw [← hh]; exact hbb i j, hsp⟩, hli, fun i => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs, hx⟩ := (hb i).2
    exact ⟨s, hs, (mem_iff_entries D N N' _).2 hx⟩
  · have hyL : y ∈ locLat D N N' p :=
      ⟨1, by simp, fun i j => by simpa using (mem_iff_entries D N N' y).1 hy i j⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.K).1
      (hsp ▸ Submodule.mem_top : y ∈ Submodule.span D.host.K (Set.range b))
    have h1 : ∀ j, c j ∈ O := fun j => hcoef c j ▸ hLL _ hyL _ (hb j).2
    choose s hs hsc using fun j => (hO _).1 (h1 j)
    have h2 : ∀ j, IsIntegral ℤ (((∏ i, s i : ℕ) : D.host.K) * c j) := by
      intro j
      obtain ⟨t, ht'⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
      rw [ht']
      rw [Nat.cast_mul, mul_comm (s j : D.host.K), mul_assoc]
      exact (isIntegral_natCast (R := ℤ) t).mul (hsc j)
    refine ⟨∏ i, s i, Nat.Coprime.prod_left fun i _ => hs i, fun j => ⟨_, h2 j⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Matrix.ext fun a c' => ?_
    simp only [Matrix.smul_apply, smul_eq, smul_eq_mul]
    change _ = ((((∏ i, s i : ℕ) : D.host.K) * c j : D.host.K) : D.host.E) * _
    push_cast; ring

end GlobalTheory.OddGenus
