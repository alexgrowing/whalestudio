import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.MeanDefs
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SgSegUnique
import Formalism.PolynomialDimension.DigitClassCount

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure FixedWeightNumericalFacts (K : Cst) (X : Dat) : Prop where
  hyp' : HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar
  cb : CBoundI 4 X.p X.m X.TT X.a X.ccl X.cStar X.c4
  d0 : 4 * X.D0 K < X.c4
  d0nn : 0 ≤ X.D0 K
  d1 : 2 * X.D1 K < X.c4
  j0nn : 0 ≤ X.J0 K
  winA : ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.a + X.a / (((X.m : ℝ) + 1) * X.Y) + 2 * X.J0 K
  winB : ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) ≤ X.bu + 2 * X.J0 K
  jA : X.Jn K ≤ X.a
  jB : X.Jn K ≤ X.lb
  deg8 : (X.ua + X.Jn K + X.ccl) + (X.ub + X.Jn K + X.ccl) + 1 ≤ 8 * X.a
  m2 : 2 ≤ X.m

theorem flattened_weight_dominant {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) : IsDominant (flatW m al be) := by
  intro s i j hij
  unfold flatW
  by_cases hs : s ∈ TT
  · simp only [hs, dite_true]
    by_cases hi : i = 0
    · subst hi
      simp only [if_true]
      split_ifs <;> omega
    · have hj : j ≠ 0 := by
        intro h
        subst h
        exact hi (Fin.le_zero_iff.1 hij)
      simp only [hi, hj, if_false]
      by_cases hil : i = Fin.last m
      · have hjl : j = Fin.last m := by
          subst hil
          exact le_antisymm (Fin.le_last j) hij
        simp [hil, hjl]
      · simp only [hil, if_false]
        split_ifs <;> omega
  · simp [hs]

theorem factorization_bound_mono_lattices {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] (p : ℕ) (be : V → V' → Kf)
    {A B : Submodule O V} {A' B' : Submodule O V'} (h : A ≤ B) (h' : A' ≤ B') {n : ℕ} {D : ℝ}
    (hf : FactorsLE p be A A' n D) : FactorsLE p be B B' n D := by
  rcases hf with h0 | ⟨x, y, hx, hy, rest⟩
  · exact Or.inl h0
  · exact Or.inr ⟨x, y, fun i => h (hx i), fun i => h' (hy i), rest⟩

theorem scaled_submodule_mono_exponent {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (w : O) (hw : algebraMap O Kf w ≠ 0) (M : Submodule O X) {t t' : ℕ}
    (h : t ≤ t') :
    scale (algebraMap O Kf w ^ (-(t : ℤ))) M ≤ scale (algebraMap O Kf w ^ (-(t' : ℤ))) M := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨w ^ (t' - t) • y, M.smul_mem _ hy, ?_⟩
  simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  rw [← algebraMap_smul Kf (w ^ (t' - t)) y, smul_smul, map_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_add₀ hw]
  congr 1
  omega

theorem uniformizer_image_ne_zero {p n' : ℕ} (R : RS p n') : algebraMap R.O R.Kf R.w ≠ 0 := by
  have hf : IsFractionRing R.O R.Kf := R.std.1.frac_O
  have hw : R.w ≠ 0 := R.std.2.1.ne_zero
  exact fun h => hw ((IsFractionRing.injective R.O R.Kf) (by rw [h, map_zero]))

theorem factorization_bound_mono_level {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) {t t' : ℕ} (h : t ≤ t')
    (c : ℕ) (e : Edge R.W R.Qq (m + 1)) {n : ℕ} {D : ℝ} (hf : FacL R lam0 t c e n D) : FacL R lam0 t' c e n D := by
  unfold FacL at *
  refine factorization_bound_mono_lattices p _ ?_ ?_ hf
  · unfold CCL
    exact inf_le_inf (inf_le_inf (scaled_submodule_mono_exponent _ (uniformizer_image_ne_zero R) _ h) le_rfl) le_rfl
  · unfold CCL'
    exact inf_le_inf (inf_le_inf (scaled_submodule_mono_exponent _ (uniformizer_image_ne_zero R) _ h) le_rfl) le_rfl

theorem infimum_kappa_le_of_rho_bound (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) (κ : ℝ) (h0 : 0 ≤ κ)
    (h : RhoL R (flatW X.m al be) (X.tStar K al be) X.c4 (X.D1 K) ((1 - κ) * dL R (flatW X.m al be))) :
    X.kF K R al be ≤ κ :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨h0, h⟩

theorem sum_dimensions_flattened_weights (hD : RestDims) {p n' : ℕ} (R : RS p n') (m : ℕ) (hm : 1 ≤ m) (TT : Finset (Fin n'))
    (A B : TT → ℕ) :
    ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)),
        dL R (flatW m (fun s => A s - j s) (fun s => B s - j s)) =
      (dimHH (m := m) R.Kf TT (ex A) (ex B) : ℝ) / gaussianNumber (p ^ n') (m + 1) := by
  unfold dL
  rw [← Finset.sum_div]
  congr 1
  rw [(hD p n' R m hm TT A B).1]
  have h2 : ∀ j : TT → ℕ, dimV R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s)) =
      ∏ s, Formalism.CountingSumsFrames.dimHar m (A s - j s) (B s - j s) := fun j => (hD p n' R m hm TT _ _).2
  simp_rw [h2]
  rw [← Nat.cast_sum]
  congr 1
  rw [← Finset.prod_univ_sum (fun s : TT => Finset.range (min (A s) (B s) + 1))
    (fun s j => Formalism.CountingSumsFrames.dimHar m (A s - j) (B s - j))]
  exact Finset.prod_congr rfl fun s _ => Formalism.CountingSumsFrames.Top.levelCount m (A s) (B s)

theorem exponent_le_shifted_add {n' : ℕ} {TT : Finset (Fin n')} (B j : TT → ℕ) (J : ℕ) (hj : ∀ s, j s ≤ J) (s : Fin n') :
    (ex B s : ℝ) ≤ (ex (fun s => B s - j s) s : ℝ) + J := by
  unfold ex
  by_cases hs : s ∈ TT
  · simp only [hs, dite_true]
    have := hj ⟨s, hs⟩
    have h2 : B ⟨s, hs⟩ ≤ (B ⟨s, hs⟩ - j ⟨s, hs⟩) + J := by omega
    exact_mod_cast h2
  · simp only [hs, dite_false]
    simp

theorem initial_level_shift_bound (X : Dat) (hS : 2 ≤ numSeg X.TT) (K : Cst) (hp : 1 ≤ X.p) (hJ : 0 ≤ X.J0 K) (A B j : X.TT → ℕ)
    (hj : ∀ s, j s ≤ X.Jn K) :
    X.t0 K A B ≤ X.t0 K (fun s => A s - j s) (fun s => B s - j s) + X.N * X.J0 K := by
  unfold Dat.t0 t0I t0G4
  have hJn : (X.Jn K : ℝ) ≤ X.J0 K := Nat.floor_le hJ
  have hterm : ∀ (jj : Fin (numSeg X.TT)) (i : Fin (segS X.TT jj)),
      min (ex B (segPos X.TT jj i) : ℝ) ((ex A (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)) ≤
        min (ex (fun s => B s - j s) (segPos X.TT jj i) : ℝ)
          ((ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)) + X.J0 K := by
    intro jj i
    have hP : (1 : ℝ) ≤ (X.p : ℝ) ^ ((segDists X.TT jj).get i) := one_le_pow₀ (by exact_mod_cast hp)
    have hP0 : (0 : ℝ) < (X.p : ℝ) ^ ((segDists X.TT jj).get i) := lt_of_lt_of_le one_pos hP
    have h1 := exponent_le_shifted_add B j (X.Jn K) hj (segPos X.TT jj i)
    have h2 := exponent_le_shifted_add A j (X.Jn K) hj (segStart X.TT jj)
    have h3 : (ex A (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) ≤
        (ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) + X.J0 K := by
      have h4 : (X.Jn K : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) ≤ X.Jn K :=
        div_le_self (Nat.cast_nonneg _) hP
      calc (ex A (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)
          ≤ ((ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) + X.Jn K) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) :=
            div_le_div_of_nonneg_right h2 hP0.le
        _ = (ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) +
            (X.Jn K : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i) := add_div _ _ _
        _ ≤ _ := by linarith
    rw [← min_add_add_right]
    exact min_le_min (by linarith) h3
  have hsum : ∑ jj : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT jj),
      min (ex B (segPos X.TT jj i) : ℝ) ((ex A (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)) ≤
      (∑ jj : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT jj),
        min (ex (fun s => B s - j s) (segPos X.TT jj i) : ℝ)
          ((ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i))) +
        X.N * X.J0 K := by
    have h1 : ∑ jj : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT jj),
        min (ex B (segPos X.TT jj i) : ℝ) ((ex A (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)) ≤
        ∑ jj : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT jj),
          (min (ex (fun s => B s - j s) (segPos X.TT jj i) : ℝ)
            ((ex (fun s => A s - j s) (segStart X.TT jj) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT jj).get i)) + X.J0 K) :=
      Finset.sum_le_sum fun jj _ => Finset.sum_le_sum fun i _ => hterm jj i
    refine le_trans h1 ?_
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h2 : ∑ jj : Fin (numSeg X.TT), (segS X.TT jj : ℝ) * X.J0 K ≤ X.N * X.J0 K := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hJ
      have h3 := sg_count X.TT hS
      have h4 : ∑ jj : Fin (numSeg X.TT), segS X.TT jj ≤ ∑ jj : Fin (numSeg X.TT), (segS X.TT jj + 1) :=
        Finset.sum_le_sum fun jj _ => Nat.le_succ _
      have h5 : ∑ jj : Fin (numSeg X.TT), segS X.TT jj ≤ X.TT.card := le_trans h4 h3
      unfold Dat.N
      exact_mod_cast h5
    linarith
  linarith

theorem keyIneq_of (D : Formalism.BasicNotions.D7) (K : Cst) (hA : K.admitted D) (h61a : RhoSumLowerBoundEdge) (h60ab : RhoUpperBoundSmallDepth) (hE : RestEdge)
    (hD : RestDims) (X : Dat) (hF : FixedWeightNumericalFacts K X) (R : RS X.p X.n') : KeyIneq K X R := by
  intro A hAm B hBm
  have hAw : ∀ s, A s ∈ X.WaP K := fun s => (Fintype.mem_piFinset.1 hAm) s
  have hBw : ∀ s, B s ∈ X.WbP K := fun s => (Fintype.mem_piFinset.1 hBm) s
  have hD1nn : 0 ≤ X.D1 K := by
    unfold Dat.D1
    have := hF.d0nn
    positivity
  have hp1 : 1 ≤ X.p := R.std.1.prime.one_lt.le

  obtain ⟨e₀, he₀⟩ : ∃ e : Edge R.W R.Qq (X.m + 1), IsEdge X.p X.n' 1 e := by
    by_contra hne
    push Not at hne
    have h1 := h60ab X.p X.n' R X.m (flatW X.m A B) (flattened_weight_dominant _ _ _) 0 X.c4
      (⌈dL R (flatW X.m A B)⌉₊ + 1) (X.D1 K) hD1nn hF.d1 (fun e he => absurd he (hne e))
    have h2 := Nat.le_ceil (dL R (flatW X.m A B))
    push_cast at h1
    linarith

  have hWin : WinX X.TT X.m X.Y X.a X.bl X.bu (2 * cleaningBudget K.C₀ X.m X.N₁ X.a X.b') (2 * cleaningBudget K.C₀ X.m X.N₁ X.a X.b')
      (ex A) (ex B) := by
    constructor
    · intro s hs
      have h1 := Finset.mem_Icc.1 (hAw ⟨s, hs⟩)
      have h2 : ex A s = A ⟨s, hs⟩ := by simp [ex, hs]
      rw [h2]
      refine ⟨by exact_mod_cast h1.1, ?_⟩
      have h3 : (A ⟨s, hs⟩ : ℝ) ≤ ((X.ua + X.Jn K + X.ccl : ℕ) : ℝ) := by exact_mod_cast h1.2
      exact le_trans h3 hF.winA
    · intro s hs
      have h1 := Finset.mem_Icc.1 (hBw ⟨s, hs⟩)
      have h2 : ex B s = B ⟨s, hs⟩ := by simp [ex, hs]
      rw [h2]
      refine ⟨?_, ?_⟩
      · have h3 : (X.lb : ℝ) ≤ B ⟨s, hs⟩ := by exact_mod_cast h1.1
        exact le_trans (Nat.le_ceil _) h3
      · have h3 : (B ⟨s, hs⟩ : ℝ) ≤ ((X.ub + X.Jn K + X.ccl : ℕ) : ℝ) := by exact_mod_cast h1.2
        exact le_trans h3 hF.winB
  have hrho := hA.2.1 X.p R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) X.a X.b' X.bl
    X.bu X.ccl X.Dp X.cStar (ex A) (ex B) X.c4 R.std hF.hyp' hWin hF.cb hF.d0 e₀ he₀
  have hdeg : ∀ s, A s + B s + 1 ≤ 8 * X.a := by
    intro s
    have h1 := (Finset.mem_Icc.1 (hAw s)).2
    have h2 := (Finset.mem_Icc.1 (hBw s)).2
    have h3 := hF.deg8
    omega
  obtain ⟨n, hn, hX⟩ := h61a X.p X.n' R X.m hF.m2 X.TT X.a A B hdeg _ X.c4 _ _ e₀ he₀ hF.d0nn hrho
  set t₁ : ℕ := ⌊t0I K.C₀ K.Ct X.p X.m X.TT X.G' X.N₁ X.a X.b' X.c4 (ex A) (ex B)⌋₊ with ht₁
  have hall : ∀ j : X.TT → ℕ, (∀ s, j s ≤ min (A s) (B s)) → ∀ e, IsEdge X.p X.n' 1 e →
      FacL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) t₁ X.c4 e (n j) (X.D1 K) :=
    fun j hj e he => hE X.p X.n' R X.m _ (flattened_weight_dominant _ _ _) t₁ X.c4 (n j) _ e₀ e he₀ he (hn j hj)
  have hle : ∀ j : X.TT → ℕ, (∀ s, j s ≤ min (A s) (B s)) →
      (n j : ℝ) ≤ dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) :=
    fun j hj => h60ab X.p X.n' R X.m _ (flattened_weight_dominant _ _ _) t₁ X.c4 (n j) (X.D1 K) hD1nn hF.d1 (hall j hj)
  have hsmall : ∀ j : X.TT → ℕ, (∀ s, j s ≤ X.Jn K) → ∀ s, j s ≤ min (A s) (B s) := by
    intro j hj s
    have h1 := (Finset.mem_Icc.1 (hAw s)).1
    have h2 := (Finset.mem_Icc.1 (hBw s)).1
    have h3 := hF.jA
    have h4 := hF.jB
    have h5 := hj s
    exact le_min (by omega) (by omega)
  have hle2 : ∀ j : X.TT → ℕ, (∀ s, j s ≤ X.Jn K) →
      (n j : ℝ) ≤ (1 - X.kF K R (fun s => A s - j s) (fun s => B s - j s)) *
        dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) := by
    intro j hj
    have hj' := hsmall j hj
    have h1 := hle j hj'
    set d := dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) with hd
    rcases (le_trans (Nat.cast_nonneg (n j)) h1).eq_or_lt with h0 | hpos
    · rw [← h0] at h1 ⊢
      simpa using h1
    · have ht : t₁ ≤ X.tStar K (fun s => A s - j s) (fun s => B s - j s) := by
        have h7 := initial_level_shift_bound X hF.hyp'.2.2.2.1 K hp1 hF.j0nn A B j hj
        unfold Dat.tStar
        exact le_trans (Nat.floor_le_floor h7) (Nat.floor_le_ceil _)
      have hk := infimum_kappa_le_of_rho_bound X K R (fun s => A s - j s) (fun s => B s - j s) (1 - (n j : ℝ) / d)
        (by
          have : (n j : ℝ) / d ≤ 1 := (div_le_one hpos).2 h1
          linarith)
        (fun e he => ⟨n j, by
          rw [← hd]
          have : (1 - (1 - (n j : ℝ) / d)) * d = n j := by
            field_simp
            ring
          rw [this], factorization_bound_mono_level R _ ht _ e (hall j hj' e he)⟩)
      have h2 : (n j : ℝ) / d ≤ 1 - X.kF K R (fun s => A s - j s) (fun s => B s - j s) := by linarith
      exact (div_le_iff₀ hpos).1 h2

  classical
  set S := Fintype.piFinset (fun s : X.TT => Finset.range (min (A s) (B s) + 1)) with hSdef
  set S' := Fintype.piFinset (fun _ : X.TT => Finset.range (X.Jn K + 1)) with hS'def
  have hmemS : ∀ j, j ∈ S → ∀ s, j s ≤ min (A s) (B s) := fun j hj s =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hj s))
  have hmemS' : ∀ j, j ∈ S' → ∀ s, j s ≤ X.Jn K := fun j hj s =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hj s))
  have hsub : S' ⊆ S := by
    intro j hj
    refine Fintype.mem_piFinset.2 fun s => Finset.mem_range.2 (Nat.lt_succ_iff.2 (hsmall j (hmemS' j hj) s))
  have hsum : ∑ j ∈ S, (n j : ℝ) ≤ ∑ j ∈ S, (dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) -
      (if j ∈ S' then X.kF K R (fun s => A s - j s) (fun s => B s - j s) *
        dL R (flatW X.m (fun s => A s - j s) (fun s => B s - j s)) else 0)) := by
    refine Finset.sum_le_sum fun j hj => ?_
    by_cases hj' : j ∈ S'
    · simp only [hj', if_true]
      have := hle2 j (hmemS' j hj')
      linarith
    · simp only [hj', if_false, sub_zero]
      exact hle j (hmemS j hj)
  rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub,
    sum_dimensions_flattened_weights hD R X.m (le_trans (by norm_num) hF.m2) X.TT A B] at hsum
  have hX' := le_trans hX hsum
  unfold Dat.kx
  set Hd := (dimHH (m := X.m) R.Kf X.TT (ex A) (ex B) : ℝ) / gaussianNumber (X.p ^ X.n') (X.m + 1) with hHd
  rw [mul_div_assoc, ← hHd] at hX'
  linarith [hX']

end Formalism.MainNotions.flipOneThree.Pf

end
