import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFFCnt

noncomputable section

namespace PI.VolStabS.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

private theorem ffH_single_right {M : ℕ} (J : Matrix (Fin M) (Fin M) K) (x : Fin M → K)
    (j : Fin M) :
    PI.VolStabS.ffH σ J x (Pi.single j 1) = ∑ i, σ (x i) * J i j := by
  unfold PI.VolStabS.ffH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_eq_single j]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  rw [ffH_single_right, Fintype.sum_eq_single i]
  · simp
  · intro b hb
    simp [Pi.single_apply, hb]

end matrix

private theorem isSq_comp_linearMap {K : Type} [Field K] {σ : K →+* K} {U V : Type}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {hV : V → V → K}
    (hsV : IsSq σ hV) (φ : U →ₗ[K] V) :
    IsSq σ (fun x y => hV (φ x) (φ y)) := {
  add_right x y z := by
    show hV (φ x) (φ (y + z)) = hV (φ x) (φ y) + hV (φ x) (φ z)
    rw [map_add, hsV.add_right]
  smul_right c x y := by
    show hV (φ x) (φ (c • y)) = c * hV (φ x) (φ y)
    rw [map_smul, hsV.smul_right]
  herm x y := hsV.herm (φ x) (φ y) }

theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} := by
  refine Nat.card_congr
    { toFun := fun φ => ⟨fun i => φ.1 (b i), fun i j => φ.2 (b i) (b j)⟩
      invFun := fun Y => ⟨b.constr K Y.1, fun x y =>
        (isSq_comp_linearMap hsV (b.constr K Y.1)).ext_basis hsU b
          (fun i j => by simpa only [Basis.constr_basis] using Y.2 i j) x y⟩
      left_inv := fun φ => by
        apply Subtype.ext
        apply b.ext
        intro i
        simp
      right_inv := fun Y => by
        apply Subtype.ext
        funext i
        simp }

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

private theorem card_eq_card_sq_of_finrank_two (h2 : finrank k K = 2) :
    Fintype.card K = Fintype.card k ^ 2 := by
  rw [← h2]
  exact Module.card_eq_pow_finrank

private theorem add_pow_card_eq_add_pow_card (a b : K) :
    (a + b) ^ Fintype.card k = a ^ Fintype.card k + b ^ Fintype.card k := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hprime, hn⟩ := FiniteField.card k p
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [hn]
  exact add_pow_char_pow a b p (n : ℕ)

private theorem mem_range_algebraMap_of_pow_card_eq (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hP : (X ^ Fintype.card k - X : K[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hq1
  have hsub : Finset.univ.image (algebraMap k K) ⊆
      (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, ← map_pow,
      FiniteField.pow_card, sub_self]
  have hcard : (X ^ Fintype.card k - X : K[X]).roots.toFinset.card ≤
      (Finset.univ.image (algebraMap k K)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
    calc _ ≤ Multiset.card (X ^ Fintype.card k - X : K[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ Fintype.card k - X : K[X]).natDegree := card_roots' _
      _ = Fintype.card k := FiniteField.X_pow_card_sub_X_natDegree_eq K hq1
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : d ∈ (X ^ Fintype.card k - X : K[X]).roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP, IsRoot.def, eval_sub, eval_pow, eval_X, hd, sub_self]
  rw [← heq] at hmem
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
  exact ⟨y, hy⟩

theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hfix : ∀ c : K, c ^ Fintype.card k = c → σ c = c := by
    intro c hc
    obtain ⟨d0, rfl⟩ := mem_range_algebraMap_of_pow_card_eq c hc
    exact σ.commutes d0
  have hdich : ∀ x : K, σ x = x ∨ σ x = x ^ Fintype.card k := by
    intro x
    have hs : σ x + σ x ^ Fintype.card k = x + x ^ Fintype.card k := by
      rw [← map_pow, ← map_add]
      exact hfix _ (by rw [add_pow_card_eq_add_pow_card, hqq, add_comm])
    have hm : σ x * σ x ^ Fintype.card k = x * x ^ Fintype.card k := by
      rw [← map_pow, ← map_mul]
      exact hfix _ (by rw [mul_pow, hqq, mul_comm])
    have h0 : (σ x - x) * (σ x - x ^ Fintype.card k) = 0 := by
      linear_combination σ x * hs - hm
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  intro x
  by_contra ha
  have hq0 : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  have hax : σ x = x := (hdich x).resolve_right ha
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hne (AlgEquiv.ext fun y => by simpa using hcon y)
  have hbq : σ b = b ^ Fintype.card k := (hdich b).resolve_left hb
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact ha (by rw [map_zero, zero_pow hq0])
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (map_zero σ)
  rcases hdich (x * b) with h | h
  · rw [map_mul, hax, hbq] at h
    exact hb (hbq.trans (mul_left_cancel₀ hx0 h))
  · rw [map_mul, hax, hbq, mul_pow] at h
    exact ha (hax.trans (mul_right_cancel₀ (pow_ne_zero _ hb0) h))

theorem mem_range_of_pow (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := mem_range_algebraMap_of_pow_card_eq d hd

theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  by_cases hd0 : d = 0
  · subst hd0
    rw [if_pos rfl, Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, by simp⟩, fun y => Subtype.ext ?_⟩
    rcases mul_eq_zero.mp y.2 with h | h
    · exact h
    · exact (map_eq_zero σ).mp h
  rw [if_neg hd0]
  have hK := card_eq_card_sq_of_finrank_two (k := k) (K := K) h2
  have hqq : ∀ y : K, (y ^ Fintype.card k) ^ Fintype.card k = y := fun y => by
    rw [← pow_mul, ← sq, ← hK, FiniteField.pow_card]
  have hN : ∀ t : K, t * σ t = t ^ (Fintype.card k + 1) := fun t => by
    rw [hfrob, pow_succ']
  have hfixset : Finset.univ.filter (fun e : K => σ e = e) =
      Finset.univ.image (algebraMap k K) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro he
      exact mem_range_algebraMap_of_pow_card_eq e ((hfrob e).symm.trans he)
    · rintro ⟨y, rfl⟩
      exact σ.commutes y
  have hfixcard : (Finset.univ.filter (fun e : K => σ e = e)).card = Fintype.card k := by
    rw [hfixset, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]
  have hD : (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card + 1 = Fintype.card k := by
    have hset : Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) =
        (Finset.univ.filter (fun e : K => σ e = e)).erase 0 := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      exact and_comm
    rw [hset, Finset.card_erase_add_one (by simp), hfixcard]
  have hS : (Finset.univ.filter (fun t : K => t ≠ 0)).card + 1 = Fintype.card k ^ 2 := by
    rw [Finset.filter_ne', Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ, hK]
  have hmaps : ∀ t ∈ Finset.univ.filter (fun t : K => t ≠ 0),
      t * σ t ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    refine ⟨?_, mul_ne_zero ht ((map_ne_zero σ).mpr ht)⟩
    rw [map_mul, hfrob (σ t), hfrob t, hqq, mul_comm]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ e : K, ((Finset.univ.filter (fun t : K => t ≠ 0)).filter
      (fun t => t * σ t = e)).card ≤ Fintype.card k + 1 := by
    intro e
    calc _ ≤ (nthRoots (Fintype.card k + 1) e).toFinset.card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          rw [Multiset.mem_toFinset, mem_nthRoots (Nat.succ_pos _), ← hN]
          exact ht.2
      _ ≤ Multiset.card (nthRoots (Fintype.card k + 1) e) := Multiset.toFinset_card_le _
      _ ≤ Fintype.card k + 1 := card_nthRoots _ _
  have htarget : Nat.card {t : K // t * σ t = d} =
      ((Finset.univ.filter (fun t : K => t ≠ 0)).filter (fun t => t * σ t = d)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ht
      refine ⟨?_, ht⟩
      rintro rfl
      exact hd0 (by simpa using ht.symm)
    · exact fun ht => ht.2
  rw [htarget]
  refine le_antisymm (hbound d) (not_lt.mp fun hlt => ?_)
  have hdD : d ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0) := by
    simp [hd, hd0]
  have hlt2 : (Finset.univ.filter (fun t : K => t ≠ 0)).card <
      (Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0)).card * (Fintype.card k + 1) := by
    calc (Finset.univ.filter (fun t : K => t ≠ 0)).card = _ := hsum
      _ < ∑ e ∈ Finset.univ.filter (fun e : K => σ e = e ∧ e ≠ 0), (Fintype.card k + 1) :=
          Finset.sum_lt_sum (fun e _ => hbound e) ⟨d, hdD, hlt⟩
      _ = _ := by rw [Finset.sum_const, smul_eq_mul]
  rw [← hD] at hS hlt2
  nlinarith [hS, hlt2]

end field

theorem fFInert_holds : FFInert := by
  intro k K _ _ _ _ σ hσ hrank hne h2k M a haM J hJ hJdet T hT hTdet
  classical
  haveI : Module.Finite k K := Module.finite_of_finrank_eq_succ hrank
  haveI : Finite K := Module.finite_of_finite k
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype K := Fintype.ofFinite K
  have hfrob := frob_of_ne σ hrank hne
  have hσr : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have h2K : (2 : K) ≠ 0 := by
    have h2' := (algebraMap k K).injective.ne h2k
    rwa [map_ofNat, map_zero] at h2'
  have hK : Fintype.card K = Nat.card k ^ 2 := by
    rw [Nat.card_eq_fintype_card]
    exact card_eq_card_sq_of_finrank_two hrank
  have hq0 : 0 < Nat.card k := Nat.card_pos
  have hN : ∀ d, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Nat.card k + 1 := by
    intro d hd
    rw [Nat.card_eq_fintype_card (α := k)]
    exact card_norm_fiber σ hfrob hrank d hd
  have hsV : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) J) :=
    ffH_isHS hσr J hJ hJdet
  have hsU : IsHS (σ : K →+* K) (PI.VolStabS.ffH (σ : K →+* K) T) :=
    ffH_isHS hσr T hT hTdet
  have e1 : Nat.card {X : Fin a → Fin M → K // PI.VolStabS.ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i)
            (Pi.basisFun K (Fin a) j)} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro X
    simp only [Pi.basisFun_apply, ffH_single]
    constructor
    · intro h i j
      subst h
      rfl
    · intro h
      exact Matrix.ext fun i j => h i j
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K)
    (PI.VolStabS.ffH (σ : K →+* K) T) hsU (by simp)
  have hli := linIndep_orth hsU.toIsSq f hf1 hf2
  obtain ⟨b', hb'⟩ : ∃ b' : Basis (Fin a) K (Fin a → K), ∀ i, b' i = f i := by
    rcases isEmpty_or_nonempty (Fin a) with hE | hE
    · exact ⟨Basis.empty _, fun i => isEmptyElim i⟩
    · exact ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp), fun i => by simp⟩
  have e2 := card_isom hsU.toIsSq hsV.toIsSq
    (Pi.basisFun K (Fin a))
  have e3 := card_isom hsU.toIsSq hsV.toIsSq b'
  have e4 : Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j,
        PI.VolStabS.ffH (σ : K →+* K) J (Y i) (Y j) =
          if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    have hdiag : ∀ i j, PI.VolStabS.ffH (σ : K →+* K) T (b' i) (b' j) =
        if i = j then PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i) else 0 := by
      intro i j
      rw [hb', hb']
      split_ifs with hij
      · subst hij
        rfl
      · exact hf1 i j hij
    simp only [hdiag]
  have key := e1.trans (e2.symm.trans (e3.trans e4))
  have final := card_diag (Nat.card k) hq0 hK hσr h2K hN a M haM (Fin M → K)
    (PI.VolStabS.ffH (σ : K →+* K) J) hsV (by simp)
    (fun i => PI.VolStabS.ffH (σ : K →+* K) T (f i) (f i))
    (fun i => hsU.toIsSq.self_fixed (f i)) hf2
  exact (congrArg (fun n : ℕ => (n : ℝ)) key).trans final

end PI.VolStabS.FFHS
