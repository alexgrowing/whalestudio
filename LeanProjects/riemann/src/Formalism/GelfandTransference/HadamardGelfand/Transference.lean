import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.NormUnitary
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion

open Module Submodule

noncomputable section

namespace Formalism.HadamardInequality.P

theorem tr_shortest {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Submodule ℤ E) [hQ : DiscreteTopology Q] (hne : Q ≠ ⊥) :
    ∃ q ∈ Q, q ≠ 0 ∧ ∀ q' ∈ Q, q' ≠ 0 → ‖q‖ ≤ ‖q'‖ := by
  obtain ⟨q0, hq0, hq00⟩ := (Submodule.ne_bot_iff Q).1 hne
  have hcl : IsClosed (Q : Set E) := by
    rw [← Submodule.coe_toAddSubgroup]; exact AddSubgroup.isClosed_of_discrete
  have hfin : (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hcl
  set S := (Metric.closedBall (0 : E) ‖q0‖ ∩ (Q : Set E)) \ {0} with hS
  have hSfin : S.Finite := hfin.sdiff
  have hq0S : q0 ∈ S := ⟨⟨by simp, hq0⟩, hq00⟩
  obtain ⟨q, hqS, hmin⟩ := Set.exists_min_image S (fun x => ‖x‖) hSfin ⟨q0, hq0S⟩
  refine ⟨q, hqS.1.2, hqS.2, fun q' hq' hq'0 => ?_⟩
  by_cases hle : ‖q'‖ ≤ ‖q0‖
  · exact hmin q' ⟨⟨by simpa using hle, hq'⟩, hq'0⟩
  · exact (hmin q0 hq0S).trans (le_of_lt (not_le.1 hle))

theorem tr_step {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ∀ m' ∈ M, Wᗮ.starProjection m' ≠ 0 →
        ‖Wᗮ.starProjection m‖ ≤ ‖Wᗮ.starProjection m'‖ := by
  obtain ⟨hsat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  set S := Formalism.F.satur M N with hSdef
  have hSW : span ℝ (S : Set E) = W := by
    rw [← hNW]
    refine le_antisymm (span_le.2 fun x hx => (Submodule.mem_inf.1 hx).2) (span_mono hNS)
  have hQd : DiscreteTopology (Formalism.F.quot M S) := (Formalism.F.degree_quotient E M S hMd hsat).1
  set Q := Formalism.F.quot M S with hQdef
  have hmemQ : ∀ q, q ∈ Q ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [hQdef, Formalism.F.quot, hSW]
  have hsubW : ∀ x, x - Wᗮ.starProjection x ∈ W := by
    intro x
    have := sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [orthogonal_orthogonal] at this
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hW
    rw [eq_top_iff, ← hspan, span_le]
    intro m hm
    have h0 : Wᗮ.starProjection m = 0 := by
      have : Wᗮ.starProjection m ∈ Q := (hmemQ _).2 ⟨m, hm, rfl⟩
      rw [hQ] at this
      exact (Submodule.mem_bot ℤ).1 this
    have := hsubW m
    rwa [h0, sub_zero] at this
  obtain ⟨q, hqQ, hq0, hqmin⟩ := tr_shortest Q hQne
  obtain ⟨m, hm, rfl⟩ := (hmemQ q).1 hqQ
  exact ⟨m, hm, hq0, fun m' hm' h0 => hqmin _ ((hmemQ _).2 ⟨m', hm', rfl⟩) h0⟩

theorem tr_chain {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) :
    ∀ k, k ≤ finrank ℝ E → ∃ (b : Fin k → E) (t : Fin k → ℝ), (∀ i, b i ∈ M) ∧
      LinearIndependent ℝ b ∧ (∀ i, 0 < t i) ∧
      (∀ i, 4 * ‖b i‖ ^ 2 ≤ 3 * t i ^ 2 + ∑ l, t l ^ 2) ∧
      (∀ i : Fin k, ∃ W : Submodule ℝ E, finrank ℝ W = i.val ∧
          ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t i ≤ ‖Wᗮ.starProjection m‖) ∧
      (∀ w ∈ span ℝ (Set.range b), ∃ z ∈ span ℤ (Set.range b),
        4 * ‖w - z‖ ^ 2 ≤ ∑ l, t l ^ 2) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, linearIndependent_empty_type,
      fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro w hw
    have hr : Set.range (Fin.elim0 : Fin 0 → E) = ∅ := Set.range_eq_empty _
    rw [hr, Submodule.span_empty, Submodule.mem_bot] at hw
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp [hw]
  | succ k ih =>
    intro hk
    obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, hcov⟩ := ih (by omega)
    set W := span ℝ (Set.range b) with hWdef
    set N := span ℤ (Set.range b) with hNdef
    have hNM : N ≤ M := span_le.2 (Set.range_subset_iff.2 hbM)
    have hNW : span ℝ (N : Set E) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
    have hNWle : ∀ z ∈ N, z ∈ W := fun z hz => by
      rw [← hNW]; exact Submodule.subset_span hz
    have hWrk : finrank ℝ W = k := by
      rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
    have hWtop : W ≠ ⊤ := by
      intro h
      have : finrank ℝ W = finrank ℝ E := by rw [h, finrank_top]
      omega
    obtain ⟨m, hm, hq0, hqmin⟩ := tr_step M hspan W N hNM hNW hWtop
    set q := Wᗮ.starProjection m with hqdef
    set S := ∑ l, t l ^ 2 with hSdef
    have hqW : q ∈ Wᗮ := starProjection_apply_mem _ _
    have hwW : m - q ∈ W := by
      have := sub_starProjection_mem_orthogonal (K := Wᗮ) m
      rwa [orthogonal_orthogonal] at this
    obtain ⟨z, hzN, hz⟩ := hcov (m - q) hwW
    set b' := m - z with hb'
    have hb'M : b' ∈ M := M.sub_mem hm (hNM hzN)
    have hdecomp : b' = q + (m - q - z) := by rw [hb']; abel
    have hezW : m - q - z ∈ W := W.sub_mem hwW (hNWle z hzN)
    have horth : ∀ e ∈ W, inner ℝ q e = 0 := fun e he => by
      rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal he hqW
    have hqpos : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have hb'n : 4 * ‖b'‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 + S := by
      rw [hdecomp, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (horth _ hezW)]
      have : m - q - z = m - q - z := rfl
      nlinarith
    have hb'W : b' ∉ W := by
      intro hW'
      apply hq0
      have hqW' : q ∈ W := by
        have : q = b' - (m - q - z) := by rw [hdecomp]; abel
        rw [this]; exact W.sub_mem hW' hezW
      exact inner_self_eq_zero.1 (horth q hqW')
    have hsum : ∑ l, (Fin.snoc (α := fun _ => ℝ) t ‖q‖ l) ^ 2 = S + ‖q‖ ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp [hSdef]
    refine ⟨Fin.snoc b b', Fin.snoc (α := fun _ => ℝ) t ‖q‖, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hb'M
      · simpa using hbM j
    · exact linearIndependent_finSnoc.2 ⟨hli, hb'W⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hqpos
      · simpa using ht0 j
    · intro i
      rw [hsum]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Fin.snoc_last]
        linarith
      · simp only [Fin.snoc_castSucc]
        have := hbn j
        nlinarith [sq_nonneg ‖q‖]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · refine ⟨W, by simpa using hWrk, fun m' hm' h0 => ?_⟩
        simpa using hqmin m' hm' h0
      · obtain ⟨W', hW'r, hW'm⟩ := hWs j
        exact ⟨W', by simpa using hW'r, fun m' hm' h0 => by simpa using hW'm m' hm' h0⟩
    · intro w' hw'
      rw [hsum]
      rw [Fin.range_snoc, Submodule.mem_span_insert] at hw'
      obtain ⟨c0, w0, hw0, rfl⟩ := hw'
      set c : ℤ := round c0 with hc
      set s : ℝ := c0 - c with hs
      have hsabs : |s| ≤ 1 / 2 := abs_sub_round c0
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := sq_abs s
        nlinarith [abs_nonneg s]
      set w1 := w0 + s • (m - q - z) with hw1
      have hw1W : w1 ∈ W := W.add_mem hw0 (W.smul_mem _ hezW)
      obtain ⟨z1, hz1N, hz1⟩ := hcov w1 hw1W
      refine ⟨c • b' + z1, ?_, ?_⟩
      · rw [Fin.range_snoc, Submodule.mem_span_insert]
        exact ⟨c, z1, hz1N, rfl⟩
      · have heq : c0 • b' + w0 - (c • b' + z1) = s • q + (w1 - z1) := by
          rw [← Int.cast_smul_eq_zsmul ℝ, hw1, hs]
          conv_lhs => rw [hdecomp]
          simp only [sub_smul, smul_add, smul_sub]
          abel
        have hw1z1 : w1 - z1 ∈ W := W.sub_mem hw1W (hNWle z1 hz1N)
        rw [heq, Formalism.NormUnitaryCountingLemmas.norm_add_sq_eq_of_inner_eq_zero (by
          rw [real_inner_smul_left, horth _ hw1z1, mul_zero]), norm_smul, Real.norm_eq_abs,
          mul_pow, sq_abs]
        have hqq : 0 ≤ ‖q‖ ^ 2 := sq_nonneg _
        nlinarith

theorem tr_dual {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Submodule ℤ E) (hspan : span ℝ (M : Set E) = ⊤)
    (W : Submodule ℝ E) {t : ℝ} (ht : 0 < t)
    (hmin : ∀ m ∈ M, Wᗮ.starProjection m ≠ 0 → t ≤ ‖Wᗮ.starProjection m‖) :
    ∃ y : Fin (finrank ℝ Wᗮ) → E, (∀ j, y j ∈ Formalism.HadamardInequality.zdual M) ∧ LinearIndependent ℝ y ∧
      ∀ j, ‖y j‖ ≤ (finrank ℝ Wᗮ : ℝ) ^ ((3 : ℝ) / 2) / t := by
  let P : E →ₗ[ℝ] Wᗮ := (Wᗮ.orthogonalProjectionOnto : E →L[ℝ] Wᗮ).toLinearMap
  have hP : ∀ x : E, ((P x : Wᗮ) : E) = Wᗮ.starProjection x := fun x => rfl
  let Q' : Submodule ℤ Wᗮ := M.map (P.restrictScalars ℤ)
  have hmemQ : ∀ x : Wᗮ, x ∈ Q' ↔ ∃ m ∈ M, P m = x := by
    intro x; simp [Q']
  have hQnorm : ∀ x ∈ Q', x ≠ 0 → t ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨m, hm, rfl⟩ := (hmemQ x).1 hx
    have h1 : Wᗮ.starProjection m ≠ 0 := by
      rw [← hP]; exact_mod_cast hx0
    have := hmin m hm h1
    rw [← hP] at this
    simpa using this
  have hQd : DiscreteTopology Q' := Formalism.NormUnitaryCountingLemmas.discreteTopology_of_norm_ge Q' ht hQnorm
  have hQl : IsZLattice ℝ Q' := ⟨by
    rw [eq_top_iff]
    intro x _
    have hx : (x : E) ∈ span ℝ (M : Set E) := by rw [hspan]; trivial
    have hPx : P (x : E) = x := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
    rw [← hPx]
    have : P (x : E) ∈ (span ℝ (M : Set E)).map P := Submodule.mem_map_of_mem hx
    rw [Submodule.map_span] at this
    refine span_mono ?_ this
    rintro _ ⟨m, hm, rfl⟩
    exact (hmemQ _).2 ⟨m, hm, rfl⟩⟩
  obtain ⟨hXd, hXl⟩ := Formalism.H.dualIsLattice (Wᗮ) Q'
  have := @hXl hXd
  have hDD := Formalism.H.dualDual (Wᗮ) Q'
  obtain ⟨v, hvX, hvli, hvn⟩ := Formalism.NormUnitaryCountingLemmas.Final.gn1 Wᗮ (Formalism.H.dual Q') hXd IsZLattice.span_top
    t ht (by
      intro y hy0 hint
      have hyQ : y ∈ Q' := by
        rw [← hDD, LinearMap.BilinForm.mem_dualSubmodule]
        intro x hx
        obtain ⟨z, hz⟩ := hint x hx
        rw [Submodule.mem_one]
        exact ⟨z, by rw [algebraMap_int_eq, eq_intCast, ← hz]; exact real_inner_comm _ _⟩
      exact hQnorm y hyQ hy0)
  refine ⟨fun j => (v j : E), fun j => ?_, ?_, fun j => ?_⟩
  · intro x hx
    have h := (LinearMap.BilinForm.mem_dualSubmodule _).1 (hvX j) (P x) ((hmemQ _).2 ⟨x, hx, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 h
    refine ⟨z, ?_⟩
    rw [algebraMap_int_eq, eq_intCast] at hz
    change (z : ℝ) = inner ℝ (v j) (P x) at hz
    have e1 : inner ℝ x (v j : E) = inner ℝ (P x) (v j) :=
      (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (v j) x).symm
    show inner ℝ x (v j : E) = z
    rw [e1, real_inner_comm, hz]
  · exact hvli.map' Wᗮ.subtype (Submodule.ker_subtype _)
  · simpa using hvn j

theorem tr_succMin_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) {i : ℕ} {r : ℝ} (v : Fin i → E) (hv : ∀ j, v j ∈ L)
    (hli : LinearIndependent ℝ v) (hr : 0 ≤ r) (hn : ∀ j, ‖v j‖ ≤ r) :
    Formalism.HadamardInequality.succMin L i ≤ r :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hr, v, hv, hli, hn⟩

theorem tr_succMin_nonneg {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (i : ℕ) : 0 ≤ Formalism.HadamardInequality.succMin L i :=
  Real.sInf_nonneg fun _ hx => hx.1

theorem transference_principle : Formalism.HadamardInequality.Transference := by
  intro E _ _ _ M hMd hspan i hi1 hin
  set n := finrank ℝ E with hn
  set k := n + 1 - i with hk
  have hkn : k ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨b, t, hbM, hli, ht0, hbn, hWs, -⟩ := tr_chain M hspan k hkn
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ t
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  set T := t j0 with hT
  have hTpos : 0 < T := ht0 j0
  have htT : ∀ l, t l ^ 2 ≤ T ^ 2 := fun l =>
    pow_le_pow_left₀ (ht0 l).le (hj0 l (Finset.mem_univ _)) 2
  have hS : ∑ l, t l ^ 2 ≤ (k : ℝ) * T ^ 2 := by
    calc ∑ l, t l ^ 2 ≤ ∑ _l : Fin k, T ^ 2 := Finset.sum_le_sum fun l _ => htT l
      _ = (k : ℝ) * T ^ 2 := by simp
  set R := Real.sqrt (((k : ℝ) + 3) / 4 * T ^ 2) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hbR : ∀ j, ‖b j‖ ≤ R := by
    intro j
    have h1 := hbn j
    have h2 := htT j
    have h3 : ‖b j‖ ^ 2 ≤ ((k : ℝ) + 3) / 4 * T ^ 2 := by nlinarith
    have := Real.abs_le_sqrt h3
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hMk : Formalism.HadamardInequality.succMin M k ≤ R := tr_succMin_le M b hbM hli hR0 hbR
  obtain ⟨W, hWr, hWm⟩ := hWs j0
  obtain ⟨y, hyD, hyli, hyn⟩ := tr_dual M hspan W hTpos hWm
  have hfr : finrank ℝ W + finrank ℝ Wᗮ = n := Submodule.finrank_add_finrank_orthogonal W
  have hj0k := j0.2
  have hij : i ≤ finrank ℝ Wᗮ := by omega
  have hWn : finrank ℝ Wᗮ ≤ n := by omega
  set A := (n : ℝ) ^ ((3 : ℝ) / 2) / T with hA
  have hA0 : 0 ≤ A := by positivity
  have hyA : ∀ j, ‖y (Fin.castLE hij j)‖ ≤ A := by
    intro j
    refine (hyn _).trans (div_le_div_of_nonneg_right ?_ hTpos.le)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hWn) (by norm_num)
  have hDi : Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i ≤ A :=
    tr_succMin_le _ (fun j => y (Fin.castLE hij j)) (fun j => hyD _)
      (hyli.comp _ (Fin.castLE_injective hij)) hA0 hyA
  have hAR : A * R ≤ (n : ℝ) ^ 2 := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hA2 : A ^ 2 = (n : ℝ) ^ 3 / T ^ 2 := by
      rw [hA, div_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hn0]
      norm_num
    have hR2 : R ^ 2 = ((k : ℝ) + 3) / 4 * T ^ 2 := Real.sq_sqrt (by positivity)
    have hk' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    rw [← pow_le_pow_iff_left₀ (mul_nonneg hA0 hR0) (by positivity) two_ne_zero]
    rw [mul_pow, hA2, hR2]
    have e : (n : ℝ) ^ 3 / T ^ 2 * (((k : ℝ) + 3) / 4 * T ^ 2) =
        (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) := by
      field_simp
    rw [e]
    have h4 : ((k : ℝ) + 3) / 4 ≤ n := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith
    calc (n : ℝ) ^ 3 * (((k : ℝ) + 3) / 4) ≤ (n : ℝ) ^ 3 * n :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = ((n : ℝ) ^ 2) ^ 2 := by ring
  calc Formalism.HadamardInequality.succMin (Formalism.HadamardInequality.zdual M) i * Formalism.HadamardInequality.succMin M k ≤ A * R :=
        mul_le_mul hDi hMk (tr_succMin_nonneg _ _) hA0
    _ ≤ (n : ℝ) ^ 2 := hAR

end Formalism.HadamardInequality.P
