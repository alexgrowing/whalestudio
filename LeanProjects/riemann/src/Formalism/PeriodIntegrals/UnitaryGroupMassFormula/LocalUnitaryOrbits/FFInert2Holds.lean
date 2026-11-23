import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS

noncomputable section

namespace PI.OmLocU.CntFF

open Module PI.VolStabSW PI.VolStabSW.FFHS

section basic

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

theorem exists_aniso2 (h2 : ∃ z : K, z + σ z ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨z, hz⟩ := h2
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra hy
    push_neg at hy
    exact hx (hs.nondeg x hy)
  have hσσ : σ (σ (h x y)) = h x y := by
    rw [← hs.herm x y, ← hs.herm y x]
  have hxu : h x (x + (z * (h x y)⁻¹) • y) = z * (h x y)⁻¹ * h x y := by
    rw [hs.add_right, hs.smul_right, hne x, zero_add]
  have hyu : h y (x + (z * (h x y)⁻¹) • y) = σ (h x y) := by
    rw [hs.add_right, hs.smul_right, hne y, mul_zero, add_zero, hs.herm x y]
  have key := hne (x + (z * (h x y)⁻¹) • y)
  rw [hs.add_right, hs.smul_right, hs.herm x (x + (z * (h x y)⁻¹) • y),
    hs.herm y (x + (z * (h x y)⁻¹) • y), hxu, hyu, hσσ, inv_mul_cancel_right₀ hy] at key
  exact hz (by rw [add_comm]; exact key)

end basic

theorem exists_orth2 {K : Type} [Field K] {σ : K →+* K} (h2 : ∃ z : K, z + σ z ≠ 0) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := by
      have : 0 < finrank K V := by omega
      exact finrank_pos_iff_exists_ne_zero.mp this
    obtain ⟨e, he⟩ := exists_aniso2 h2 hs x hx
    obtain ⟨g, hg1, hg2⟩ := ih (perp hs.toIsSq e) (fun w w' => h w w') (perp_isHS hs e he)
      (by have := finrank_perp hs.toIsSq e he; omega)
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact (mem_perp hs.toIsSq e _).mp (g j).2
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hs.herm e (g i : V), (mem_perp hs.toIsSq e _).mp (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun h' => hij (by rw [h']))
    · intro i
      cases i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem card_norm2 (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∃ z : K, z + σ z ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ c, σ c = c →
      (Nat.card {x : V // h x x = c} : ℝ) = (q : ℝ) ^ (2 * (m : ℤ) - 1) +
        (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * ((if c = 0 then (q : ℝ) else 0) - 1) := by
  intro m
  induction m with
  | zero =>
    intro V _ _ _ h hs hm c hc
    have hV : ∀ x : V, x = 0 := finrank_zero_iff_forall_zero.mp hm
    have h00 : h 0 0 = 0 := by
      have h0 := hs.smul_right 0 0 0
      rwa [zero_smul, zero_mul] at h0
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    by_cases hc0 : c = 0
    · have h1 : Nat.card {x : V // h x x = c} = 1 :=
        Nat.card_eq_one_iff_exists.mpr ⟨⟨0, by rw [h00, hc0]⟩, fun y => Subtype.ext (hV y.1)⟩
      rw [h1, if_pos hc0]
      simp only [Nat.cast_zero, mul_zero, zero_sub, zpow_neg_one, pow_zero, one_mul, Nat.cast_one]
      field_simp
      try ring
    · haveI : IsEmpty {x : V // h x x = c} :=
        ⟨fun y => hc0 (by rw [← y.2, hV y.1, h00])⟩
      rw [Nat.card_of_isEmpty, if_neg hc0]
      simp only [Nat.cast_zero, mul_zero, zero_sub, zpow_neg_one, pow_zero, one_mul]
      ring
  | succ m ih =>
    intro V _ _ _ h hs hm c hc
    haveI : Finite V := Module.finite_of_finite K
    have hpos : 0 < finrank K V := by omega
    obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := finrank_pos_iff_exists_ne_zero.mp hpos
    obtain ⟨e, he⟩ := exists_aniso2 h2 hs x hx
    have hσa : σ (h e e) = h e e := (hs.herm e e).symm
    have hW : finrank K (perp hs.toIsSq e) = m := by
      have := finrank_perp hs.toIsSq e he
      omega
    have hfib : ∀ t : K, (Nat.card {w : perp hs.toIsSq e // h w w = c - σ t * t * h e e} : ℝ) =
        (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1) := fun t =>
      ih (perp hs.toIsSq e) (fun w w' => h w w') (perp_isHS hs e he) hW _
        (by rw [map_sub, map_mul, map_mul, hσ, hσa, hc]; ring)
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    have hsum : ∑ t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
          ((if c - σ t * t * h e e = 0 then (q : ℝ) else 0) - 1)) =
        (Fintype.card K : ℝ) * ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) +
          (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) * q *
            ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum, show (Fintype.card K : ℝ) *
          ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) =
          ∑ _t : K, ((q : ℝ) ^ (2 * (m : ℤ) - 1) - (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1)) by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul], ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs <;> ring
    have hN0 : ((Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0)).card : ℝ) =
        if c = 0 then 1 else (q : ℝ) + 1 := by
      have e1 : Finset.univ.filter (fun t : K => c - σ t * t * h e e = 0) =
          Finset.univ.filter (fun t : K => t * σ t = c * (h e e)⁻¹) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h0
          rw [eq_mul_inv_iff_mul_eq₀ he]
          linear_combination -h0
        · intro h0
          rw [eq_mul_inv_iff_mul_eq₀ he] at h0
          linear_combination -h0
      rw [e1, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        hN _ (by rw [map_mul, map_inv₀, hc, hσa])]
      by_cases hc0 : c = 0 <;> simp [hc0, he]
    have hKr : (Fintype.card K : ℝ) = (q : ℝ) ^ 2 := by rw [hK]; push_cast; ring
    have e2 : (2 * ((m + 1 : ℕ) : ℤ) - 1) = (2 * (m : ℤ) - 1) + 2 := by push_cast; ring
    have e3 : (((m + 1 : ℕ) : ℤ) - 1) = ((m : ℤ) - 1) + 1 := by push_cast; ring
    rw [card_decomp hs.toIsSq e he c, Nat.cast_sum]
    simp_rw [hfib]
    rw [hsum, hN0, hKr, e2, e3, zpow_add₀ hq, zpow_add₀ hq, zpow_two, zpow_one]
    by_cases hc0 : c = 0
    · rw [if_pos hc0, if_pos hc0]
      ring
    · rw [if_neg hc0, if_neg hc0]
      ring

theorem card_diag2 (q : ℕ) (hq0 : 0 < q) (hK : Fintype.card K = q ^ 2) (hσ : ∀ x, σ (σ x) = x)
    (h2 : ∃ z : K, z + σ z ≠ 0)
    (hN : ∀ d, σ d = d → Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else q + 1) :
    ∀ (a m : ℕ), a ≤ m → ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (h : V → V → K), IsHS σ h → finrank K V = m → ∀ d : Fin a → K, (∀ i, σ (d i) = d i) →
      (∀ i, d i ≠ 0) →
      (Nat.card {Y : Fin a → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - j) - 1) - (-1) ^ (m - j) * (q : ℝ) ^ (m - j - 1)) := by
  classical
  intro a
  induction a with
  | zero =>
    intro m _ V _ _ _ h hs hm d _ _
    have h1 : Nat.card {Y : Fin 0 → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} = 1 :=
      Nat.card_eq_one_iff_exists.mpr ⟨⟨Fin.elim0, fun i => Fin.elim0 i⟩,
        fun y => Subtype.ext (funext fun i => Fin.elim0 i)⟩
    rw [h1]
    simp
  | succ a ih =>
    intro m ham V _ _ _ h hs hm d hd hd0
    haveI : Finite V := Module.finite_of_finite K
    let e : {Y : Fin (a + 1) → V // ∀ i j, h (Y i) (Y j) = if i = j then d i else 0} ≃
        Σ y : {x : V // h x x = d 0}, {Y' : Fin a → perp hs.toIsSq y.1 //
          ∀ i j, h (Y' i : V) (Y' j) = if i = j then d i.succ else 0} :=
      { toFun := fun Y => ⟨⟨Y.1 0, by simpa using Y.2 0 0⟩,
          ⟨fun i => ⟨Y.1 i.succ, (mem_perp hs.toIsSq _ _).mpr
            (by simpa [(Fin.succ_ne_zero i).symm] using Y.2 0 i.succ)⟩,
           fun i j => by simpa [Fin.succ_inj] using Y.2 i.succ j.succ⟩⟩
        invFun := fun p => ⟨Fin.cons p.1.1 (fun i => (p.2.1 i : V)), fun i j => by
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => simpa using p.1.2
            | succ j =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero j).symm]
              exact (mem_perp hs.toIsSq _ _).mp (p.2.1 j).2
          | succ i =>
            cases j using Fin.cases with
            | zero =>
              simp only [Fin.cons_zero, Fin.cons_succ]
              rw [if_neg (Fin.succ_ne_zero i), hs.herm, (mem_perp hs.toIsSq _ _).mp (p.2.1 i).2,
                map_zero]
            | succ j =>
              simp only [Fin.cons_succ]
              rw [p.2.2 i j]
              simp [Fin.succ_inj]⟩
        left_inv := fun Y => by
          apply Subtype.ext
          funext i
          cases i using Fin.cases <;> rfl
        right_inv := fun p => by
          rcases p with ⟨⟨y, hy⟩, ⟨Y', hY'⟩⟩
          rfl }
    haveI : Fintype {x : V // h x x = d 0} := Fintype.ofFinite _
    have hfib : ∀ y : {x : V // h x x = d 0},
        (Nat.card {Y' : Fin a → perp hs.toIsSq y.1 //
          ∀ i j, h (Y' i : V) (Y' j) = if i = j then d i.succ else 0} : ℝ) =
        ∏ j : Fin a, ((q : ℝ) ^ (2 * (m - 1 - j) - 1) - (-1) ^ (m - 1 - j) * (q : ℝ) ^ (m - 1 - j - 1)) :=
      fun y => ih (m - 1) (by omega) (perp hs.toIsSq y.1) (fun w w' => h w w')
        (perp_isHS hs y.1 (by rw [y.2]; exact hd0 0))
        (by have := finrank_perp hs.toIsSq y.1 (by rw [y.2]; exact hd0 0); omega)
        (fun i => d i.succ) (fun i => hd i.succ) (fun i => hd0 i.succ)
    have hS := card_norm2 q hq0 hK hσ h2 hN m V h hs hm (d 0) (hd 0)
    have hfirst : (q : ℝ) ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q : ℝ) ^ ((m : ℤ) - 1) *
        ((if d 0 = 0 then (q : ℝ) else 0) - 1) =
        (q : ℝ) ^ (2 * (m - ((0 : Fin (a + 1)) : ℕ)) - 1) -
          (-1) ^ (m - ((0 : Fin (a + 1)) : ℕ)) * (q : ℝ) ^ (m - ((0 : Fin (a + 1)) : ℕ) - 1) := by
      rw [if_neg (hd0 0), Fin.val_zero, Nat.sub_zero]
      have e1 : (2 * (m : ℤ) - 1) = ((2 * m - 1 : ℕ) : ℤ) := by omega
      have e2 : ((m : ℤ) - 1) = ((m - 1 : ℕ) : ℤ) := by omega
      rw [e1, e2, zpow_natCast, zpow_natCast]
      ring
    rw [Nat.card_congr e, Nat.card_sigma, Nat.cast_sum, Finset.sum_congr rfl (fun y _ => hfib y),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hS, hfirst,
      Fin.prod_univ_succ]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [Fin.val_succ, show m - (↑j + 1) = m - 1 - ↑j by omega]

def FFInert2 : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))

theorem exists_tr_ne {k K : Type} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (hne : σ ≠ AlgEquiv.refl) : ∃ z : K, z + (σ : K →+* K) z ≠ 0 := by
  by_contra hall
  push_neg at hall
  apply hne
  ext z
  have h1 : (1 : K) + 1 = 0 := by
    have h1' := hall 1
    change (1 : K) + σ 1 = 0 at h1'
    rwa [map_one] at h1'
  have h2' : z + σ z = 0 := hall z
  show σ z = z
  linear_combination h2' - z * h1

theorem fFInert2_holds : FFInert2 := by
  intro k K _ _ _ _ σ hσ hrank hne M a haM J hJ hJd T hT hTd
  classical
  haveI : Fintype k := Fintype.ofFinite k
  haveI : FiniteDimensional k K := Module.finite_of_finrank_pos (by omega)
  haveI : Finite K := Module.finite_of_finite k
  haveI : Fintype K := Fintype.ofFinite K
  have hq0 : 0 < Fintype.card k := Fintype.card_pos
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), hrank]
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := hσ
  have h2 := exists_tr_ne σ hne
  have hfrob := frob_of_ne σ hrank hne
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1 :=
    fun d hd => card_norm_fiber σ hfrob hrank d hd
  have hTs := ffH_isHS hσ' T hT hTd
  obtain ⟨f, hf1, hf2⟩ := exists_orth2 h2 a (Fin a → K) (ffH (σ : K →+* K) T) hTs
    (Module.finrank_fin_fun K)
  have hPu : IsUnit (Matrix.of f) :=
    (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of f)).mp
      (linIndep_orth hTs.toIsSq f hf1 hf2)
  have hPdet : IsUnit (Matrix.of f).det := (Matrix.isUnit_iff_isUnit_det _).mp hPu
  have hPm : IsUnit ((Matrix.of f).map (σ : K →+* K)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      ((RingHom.map_det (σ : K →+* K) (Matrix.of f)) ▸ hPdet.map (σ : K →+* K))
  have hPt : IsUnit (Matrix.transpose (Matrix.of f)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr ((Matrix.det_transpose (Matrix.of f)).symm ▸ hPdet)
  have hG : ∀ {b c : ℕ} (A : Matrix (Fin c) (Fin c) K) (X : Matrix (Fin b) (Fin c) K),
      ffGram (σ : K →+* K) A X = X.map (σ : K →+* K) * A * Matrix.transpose X := by
    intro b c A X
    ext i j
    simp only [ffGram, ffH, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Finset.sum_mul]
    exact Finset.sum_comm
  have hD : ∀ i j, ffGram (σ : K →+* K) T (Matrix.of f) i j =
      if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      rfl
    · rw [if_neg hij]
      exact hf1 i j hij
  let E : (Fin a → Fin M → K) ≃ (Fin a → Fin M → K) :=
    { toFun := fun X => (Matrix.of f * Matrix.of X : Matrix (Fin a) (Fin M) K)
      invFun := fun Y => ((Matrix.of f)⁻¹ * Matrix.of Y : Matrix (Fin a) (Fin M) K)
      left_inv := fun X => by
        change (Matrix.of f)⁻¹ * (Matrix.of f * Matrix.of X) = Matrix.of X
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPdet, Matrix.one_mul]
      right_inv := fun Y => by
        change Matrix.of f * ((Matrix.of f)⁻¹ * Matrix.of Y) = Matrix.of Y
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.one_mul] }
  have hiff : ∀ X : Fin a → Fin M → K, ffGram (σ : K →+* K) J X = T ↔
      ∀ i j, ffH (σ : K →+* K) J (E X i) (E X j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0 := by
    intro X
    have hG1 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
        (Matrix.of f).map (σ : K →+* K) * ffGram (σ : K →+* K) J X * Matrix.transpose (Matrix.of f) := by
      rw [hG J (Matrix.of f * Matrix.of X), hG J X, Matrix.map_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      try rfl
    have hD' : ffGram (σ : K →+* K) T (Matrix.of f) =
        (Matrix.of f).map (σ : K →+* K) * T * Matrix.transpose (Matrix.of f) := hG T (Matrix.of f)
    constructor
    · intro hX i j
      have h3 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
          ffGram (σ : K →+* K) T (Matrix.of f) := by
        rw [hG1, hX, hD']
      exact (congrFun (congrFun h3 i) j).trans (hD i j)
    · intro hY
      have h3 : ffGram (σ : K →+* K) J (Matrix.of f * Matrix.of X) =
          ffGram (σ : K →+* K) T (Matrix.of f) := by
        ext i j
        exact (hY i j).trans (hD i j).symm
      rw [hG1, hD'] at h3
      exact hPm.mul_left_cancel (hPt.mul_right_cancel h3)
  have hcd := card_diag2 (Fintype.card k) hq0 hK hσ' h2 hN a M haM (Fin M → K)
    (ffH (σ : K →+* K) J) (ffH_isHS hσ' J hJ hJd) (Module.finrank_fin_fun K)
    (fun i => ffH (σ : K →+* K) T (f i) (f i))
    (fun i => (hTs.herm (f i) (f i)).symm) (fun i => hf2 i)
  have hE : {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} ≃
      {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0} :=
    E.subtypeEquiv hiff
  rw [Nat.card_congr hE]
  rw [hcd]
  rw [Nat.card_eq_fintype_card]

end PI.OmLocU.CntFF
