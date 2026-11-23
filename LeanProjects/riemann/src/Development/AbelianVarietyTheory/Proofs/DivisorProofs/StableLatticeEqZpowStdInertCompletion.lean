import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open IsDedekindDomain NumberField
open scoped Matrix

namespace GlobalTheory.LocLatInert

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_unit_of_inert (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∃ u : K, σ u * u = 1 ∧ Valued.v u ≤ 1 ∧ Valued.v (σ u) ≤ 1 ∧ 1 - u ≠ 0 ∧
      Valued.v (1 - u)⁻¹ ≤ 1 := by
  obtain ⟨x, hx1, hx2⟩ := hx

  have hvx : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (σ x - x) := hx2.symm
      _ ≤ max (Valued.v (σ x)) (Valued.v x) := Valuation.map_sub _ _ _
      _ = Valued.v x := by rw [hv, max_self]
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvx; exact zero_ne_one hvx
  have hsx0 : σ x ≠ 0 := by
    intro h0; rw [← hv, h0, map_zero] at hvx; exact zero_ne_one hvx
  have hd : x - σ x ≠ 0 := by
    intro h0
    rw [← neg_sub, h0, neg_zero, map_zero] at hx2
    exact zero_ne_one hx2
  have hvd : Valued.v (x - σ x) = 1 := by rw [← neg_sub, Valuation.map_neg, hx2]

  refine ⟨σ x * x⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hσ]
    field_simp
  · rw [map_mul, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [map_mul, map_mul, map_inv₀, hσ, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [sub_ne_zero]
    intro h
    apply hd
    have : x = σ x := by
      field_simp at h
      exact h
    rw [← this, sub_self]
  · have e : (1 - σ x * x⁻¹)⁻¹ = x * (x - σ x)⁻¹ := by
      field_simp
    rw [e, map_mul, map_inv₀, hvx, hvd]
    simp

theorem single_mem_of_mem (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hO : ∀ a : K, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L)
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (u : K) (hu : σ u * u = 1) (hu1 : Valued.v u ≤ 1) (hu2 : Valued.v (σ u) ≤ 1)
    (hu3 : 1 - u ≠ 0) (hu4 : Valued.v (1 - u)⁻¹ ≤ 1)
    (w : Fin n → K) (hw : w ∈ L) (i : Fin n) : Pi.single i (w i) ∈ L := by

  have hdd : ∀ j, Function.update (1 : Fin n → K) i u j * Function.update (1 : Fin n → K) i (σ u) j = 1 := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self, Function.update_self, mul_comm, hu]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Pi.one_apply, mul_one]
  let D : GL (Fin n) K :=
    ⟨Matrix.diagonal (Function.update 1 i u), Matrix.diagonal (Function.update 1 i (σ u)),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; exact congrArg _ (funext hdd),
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        exact congrArg _ (funext fun j => by rw [mul_comm]; exact hdd j)⟩
  have hDU : D ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show ((Matrix.diagonal (Function.update (1 : Fin n → K) i u)).map σ)ᵀ * 1 *
      Matrix.diagonal (Function.update (1 : Fin n → K) i u) = 1
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self, hu]
    · rw [Function.update_of_ne hj, Pi.one_apply, map_one, mul_one]
  have hent : ∀ (c : K), Valued.v c ≤ 1 → ∀ a b,
      Valued.v (Matrix.diagonal (Function.update (1 : Fin n → K) i c) a b) ≤ 1 := by
    intro c hc a b
    rw [Matrix.diagonal_apply]
    split_ifs
    · by_cases ha : a = i
      · rw [ha, Function.update_self]; exact hc
      · rw [Function.update_of_ne ha, Pi.one_apply, map_one]
    · rw [map_zero]; exact zero_le
  have hDw := hU D hDU (hent u hu1) (hent (σ u) hu2) w hw

  have e1 : (D : Matrix (Fin n) (Fin n) K) *ᵥ w - w = Pi.single i ((u - 1) * w i) := by
    funext j
    show (Matrix.diagonal (Function.update (1 : Fin n → K) i u) *ᵥ w) j - w j = _
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · rw [hj, Function.update_self, Pi.single_eq_same]; ring
    · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj, Pi.one_apply, one_mul, sub_self]
  have hsub : Pi.single i ((u - 1) * w i) ∈ L := e1 ▸ L.sub_mem hDw hw

  have hc : Valued.v (-(1 - u)⁻¹) ≤ 1 := by rw [Valuation.map_neg]; exact hu4
  have hfin := hO _ hc _ hsub
  convert hfin using 1
  funext j
  by_cases hj : j = i
  · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
    field_simp
    ring
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]

theorem single_mem_swap (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (i j : Fin n) (t : K) (h : Pi.single i t ∈ L) : Pi.single j t ∈ L := by

  have hPP : (Equiv.swap i j).permMatrix K * (Equiv.swap i j).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  let P : GL (Fin n) K := ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K, hPP, hPP⟩
  have hmap : ((Equiv.swap i j).permMatrix K).map σ = (Equiv.swap i j).permMatrix K := by
    ext a b
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact map_one σ
    · exact map_zero σ
  have hPU : P ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show (((Equiv.swap i j).permMatrix K).map σ)ᵀ * 1 * (Equiv.swap i j).permMatrix K = 1
    rw [hmap, Matrix.transpose_permMatrix, Matrix.mul_one, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hent : ∀ a b, Valued.v (((Equiv.swap i j).permMatrix K) a b) ≤ 1 := by
    intro a b
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le
  have hP := hU P hPU hent hent _ h

  have e : (P : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i t = Pi.single j t := by
    show (Equiv.swap i j).permMatrix K *ᵥ Pi.single i t = Pi.single j t
    rw [Matrix.permMatrix_mulVec]
    funext a
    simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  exact e ▸ hP

end GlobalTheory.LocLatInert

namespace GlobalTheory.LocLatInert

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem set_classify (I : Set K) (hmul : ∀ a : K, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I)
    (N : K) (hN : N ≠ 0) (hNI : N ∈ I) (hb : ∀ t ∈ I, Valued.v (N * t) ≤ 1) :
    ∃ M : ℤ, ∀ t, t ∈ I ↔ Valued.v t ≤ WithZero.exp M := by
  have hvN : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).2 hN

  let S : Set ℤ := {m | ∃ t ∈ I, Valued.v t = WithZero.exp m}
  have hS : S.Nonempty := ⟨WithZero.log (Valued.v N), N, hNI, (WithZero.exp_log hvN).symm⟩
  have hbdd : BddAbove S := by
    refine ⟨-WithZero.log (Valued.v N), ?_⟩
    rintro m ⟨t, ht, hvt⟩
    have h1 := hb t ht
    rw [map_mul, hvt, ← WithZero.exp_log hvN, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    omega

  obtain ⟨t0, ht0, hvt0⟩ : sSup S ∈ S := Int.csSup_mem hS hbdd
  refine ⟨sSup S, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · by_cases h0 : t = 0
    · rw [h0, map_zero]; exact zero_le
    · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 h0
      rw [← WithZero.exp_log hvt, WithZero.exp_le_exp]
      exact le_csSup hbdd ⟨t, ht, (WithZero.exp_log hvt).symm⟩
  · have ht00 : t0 ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvt0; exact WithZero.exp_ne_zero hvt0.symm
    have e : t = (t * t0⁻¹) * t0 := by field_simp
    rw [e]
    refine hmul _ ?_ t0 ht0
    rw [map_mul, map_inv₀, hvt0]
    calc Valued.v t * (WithZero.exp (sSup S))⁻¹
        ≤ WithZero.exp (sSup S) * (WithZero.exp (sSup S))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.LocLatInert

namespace GlobalTheory.LocLatInert

theorem stable_lattice_eq_zpow_std : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  intro E _ _ P σ hσ hv hx ϖ hϖ n L N hN hO hN' hb hU
  obtain ⟨u, hu, hu1, hu2, hu3, hu4⟩ := exists_unit_of_inert σ hσ hv hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨0, fun w => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩
    have hw : w = 0 := funext fun i => i.elim0
    rw [hw]
    exact L.zero_mem
  ·
    let i0 : Fin n := ⟨0, hn⟩
    let I : Set (P.adicCompletion E) := {t | Pi.single i0 t ∈ L}
    have hIall : ∀ (i : Fin n) t, Pi.single i t ∈ L ↔ t ∈ I := fun i t =>
      ⟨single_mem_swap σ L hU i i0 t, single_mem_swap σ L hU i0 i t⟩
    have hmul : ∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I := by
      intro a ha t ht
      have e : Pi.single i0 (a * t) = a • (Pi.single i0 t : Fin n → P.adicCompletion E) := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 (a * t) ∈ L
      rw [e]
      exact hO a ha _ ht
    have hNI : N ∈ I := by
      have h1 := hN' (Pi.single i0 1) fun i => by
        by_cases hi : i = i0
        · rw [hi, Pi.single_eq_same, map_one]
        · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le
      have e : N • (Pi.single i0 1 : Fin n → P.adicCompletion E) = Pi.single i0 N := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 N ∈ L
      rw [← e]
      exact h1
    have hbI : ∀ t ∈ I, Valued.v (N * t) ≤ 1 := fun t ht => by
      have h1 := hb _ ht i0
      rwa [Pi.single_eq_same] at h1
    obtain ⟨M, hM⟩ := set_classify I hmul N hN hNI hbI

    have key : ∀ t : P.adicCompletion E, Valued.v (ϖ ^ M * t) ≤ 1 ↔ Valued.v t ≤ WithZero.exp M := by
      intro t
      rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
      constructor
      · intro h
        calc Valued.v t = WithZero.exp M * (WithZero.exp (-M) * Valued.v t) := by
              rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
          _ ≤ WithZero.exp M * 1 := by gcongr
          _ = WithZero.exp M := mul_one _
      · intro h
        calc WithZero.exp (-M) * Valued.v t ≤ WithZero.exp (-M) * WithZero.exp M := by gcongr
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    refine ⟨M, fun w => ⟨fun hw i => ?_, fun hw => ?_⟩⟩
    · exact (key (w i)).2 ((hM (w i)).1
        ((hIall i (w i)).1 (single_mem_of_mem σ L hO hU u hu hu1 hu2 hu3 hu4 w hw i)))
    · rw [← Finset.univ_sum_single w]
      exact L.sum_mem fun i _ => (hIall i (w i)).2 ((hM (w i)).2 ((key (w i)).1 (hw i)))

end GlobalTheory.LocLatInert
