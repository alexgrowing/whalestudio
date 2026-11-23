import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqF
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

noncomputable section

namespace GlobalTheory.RestDegree

theorem telescope (T : ℝ) (A K : ℕ → ℝ) (h : ∀ i, T * (A i - A (i + 1)) ≤ K i - K (i + 1) + 2) (i n : ℕ) :
    T * (A i - A (i + n)) ≤ K i - K (i + n) + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := h (i + n)
    rw [← add_assoc]
    push_cast
    linarith

theorem sum_extendByZero_fin_eq_sum_of_eq {p : ℕ} (l : Fin p → ℕ) : (∑ i, (l i : ℝ)) = ∑ i ∈ Finset.range p, (ext0 l i : ℝ) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ext0
  rw [dif_pos i.2]

theorem floor_le (T T' : ℕ) (hT : T ≤ T') (hT' : 0 < T') (c c' : ℤ) (h0 : 0 ≤ c') (hc : c ≤ c') :
    (T : ℤ) * ((Int.fdiv c T').toNat : ℤ) ≤ c' := by
  have hp : (0 : ℤ) < T' := by exact_mod_cast hT'
  have hT2 : (T : ℤ) ≤ T' := by exact_mod_cast hT
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  rcases le_total (c / T') 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simpa using h0
  · rw [Int.toNat_of_nonneg h]
    have := Int.mul_ediv_self_le (x := c) hp.ne'
    nlinarith

theorem step {p : ℕ} (T : ℕ) (g κ : Fin p → ℕ) (h : ∀ i, (T : ℤ) * g i ≤ WeightAlgebra.gapZ κ i + 2) (i : ℕ) :
    (T : ℝ) * ((ext0 (ofGaps g) i : ℝ) - ext0 (ofGaps g) (i + 1)) ≤ (ext0 κ i : ℝ) - ext0 κ (i + 1) + 2 := by
  unfold ext0
  by_cases hi : i < p
  · have h1 := h ⟨i, hi⟩
    rw [← gapZ_ofGaps g] at h1
    unfold WeightAlgebra.gapZ at h1
    by_cases hi' : i + 1 < p
    · simp only [dif_pos hi, dif_pos hi'] at h1 ⊢
      exact_mod_cast h1
    · simp only [dif_pos hi, dif_neg hi'] at h1 ⊢
      push_cast
      simp only [sub_zero]
      exact_mod_cast h1
  · have hi' : ¬ i + 1 < p := by omega
    simp [dif_neg hi, dif_neg hi']

theorem gap_nonneg {p : ℕ} {κ : Fin p → ℕ} (h : Antitone κ) (i : Fin p) : 0 ≤ WeightAlgebra.gapZ κ i := by
  unfold WeightAlgebra.gapZ
  split_ifs with hi
  · have : κ ⟨i.1 + 1, hi⟩ ≤ κ i := h (by simp [Fin.le_def])
    omega
  · positivity

theorem entry_le {p : ℕ} (T : ℕ) (g κ : Fin p → ℕ) (h : ∀ i, (T : ℤ) * g i ≤ WeightAlgebra.gapZ κ i + 2) (i : ℕ) (hi : i ≤ p) :
    (T : ℝ) * (ext0 (ofGaps g) i : ℝ) ≤ (ext0 κ i : ℝ) + 2 * p := by
  have := telescope T (fun i => (ext0 (ofGaps g) i : ℝ)) (fun i => (ext0 κ i : ℝ)) (step T g κ h) i p
  have e1 : ext0 (ofGaps g) (i + p) = 0 := by unfold ext0; rw [dif_neg (by omega)]
  have e2 : ext0 κ (i + p) = 0 := by unfold ext0; rw [dif_neg (by omega)]
  simpa [e1, e2] using this

theorem rest_bounds (A : ℕ → ℝ) (hA : Antitone A) (h0 : ∀ i, 0 ≤ A i) (n q : ℕ) :
    0 ≤ (∑ i ∈ Finset.range (n + 1 + q), A i) - ((n : ℝ) + 1) * (A n - A (n + 1)) ∧
    (∑ i ∈ Finset.range (n + 1 + q), A i) - ((n : ℝ) + 1) * (A n - A (n + 1)) ≤
      ((n : ℝ) + 1) * (A 0 - A n) + ((n : ℝ) + 1 + q) * A (n + 1) := by
  rw [Finset.sum_range_add]
  have a1 : ∑ i ∈ Finset.range (n + 1), A i ≤ (n + 1 : ℕ) • A 0 := by
    have := Finset.sum_le_card_nsmul (Finset.range (n + 1)) A (A 0) (fun i _ => hA (Nat.zero_le i))
    rwa [Finset.card_range] at this
  have a2 : (n + 1 : ℕ) • A n ≤ ∑ i ∈ Finset.range (n + 1), A i := by
    have := Finset.card_nsmul_le_sum (Finset.range (n + 1)) A (A n)
      (fun i hi => hA (by have := Finset.mem_range.1 hi; omega))
    rwa [Finset.card_range] at this
  have a3 : ∑ i ∈ Finset.range q, A (n + 1 + i) ≤ q • A (n + 1) := by
    have := Finset.sum_le_card_nsmul (Finset.range q) (fun i => A (n + 1 + i)) (A (n + 1))
      (fun i _ => hA (Nat.le_add_right _ i))
    rwa [Finset.card_range] at this
  have a4 : 0 ≤ ∑ i ∈ Finset.range q, A (n + 1 + i) := Finset.sum_nonneg fun i _ => h0 _
  simp only [nsmul_eq_mul] at a1 a2 a3
  push_cast at a1 a2
  have a5 : 0 ≤ ((n : ℝ) + 1) * A (n + 1) := mul_nonneg (by positivity) (h0 _)
  constructor <;> nlinarith

section Place

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ)

theorem mul_lGapP_le_gapZ_add_two (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) :
    (Tp.TO : ℤ) * lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ i ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) i + 2 := by
  have g0 := gap_nonneg ((kaR Tp hK j).aPlus_antitone τ) i
  unfold lGapP
  split_ifs with h
  · exact floor_le _ _ (by unfold WeightAlgebra.Tp; omega) (by unfold WeightAlgebra.Tp; omega) _ _ (by omega) le_rfl
  · refine floor_le _ _ (by unfold WeightAlgebra.Tp; omega) (by unfold WeightAlgebra.Tp; omega) _ _ (by omega) ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    have : (0 : ℤ) ≤ ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn := by positivity
    omega

theorem gapM_le (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) :
    (Tp.TO : ℤ) * lGapM D (kaR Tp hK j) Tp.TO τ i ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aM τ) i + 2 := by
  have g0 := gap_nonneg ((kaR Tp hK j).aM_anti τ) i
  unfold lGapM
  split_ifs with h
  · exact floor_le _ _ (by unfold WeightAlgebra.Tp; omega) (by unfold WeightAlgebra.Tp; omega) _ _ (by omega) le_rfl
  · refine floor_le _ _ (by unfold WeightAlgebra.Tp; omega) (by unfold WeightAlgebra.Tp; omega) _ _ (by omega) ?_
    unfold WeightAlgebra.gapZ
    rw [dif_neg h]
    omega

theorem kappa_spread (hj : InR D j) (τ : D.what₂.Tau) :
    (ext0 ((kaR Tp hK j).aP τ) 0 : ℝ) - ext0 ((kaR Tp hK j).aP τ) (D.R.k - 2) ≤ L.Sc := by
  have h1 := hj.1
  have h2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have big : ∀ (i : ℕ) (hi : i < D.R.k - 1), (ext0 ((kaR Tp hK j).aP τ) i : ℝ) =
      (((D.hc τ).v ⟨i, hi⟩ : ℚ) : ℝ) + ((DV.eQ D j τ : ℚ) : ℝ) - ((D.R.k : ℝ) + j - 1 - 1 - i) - ((D.R.t : ℝ) + 1) / 2 := by
    intro i hi
    have hi' : i < (D.R.sigW j).1 := by omega
    have e1 := kaWt_big D hK (even_nV Tp) j h1 h2 τ ⟨i, hi'⟩
    have e2 := (hK j h1 h2 τ).1 ⟨i, hi'⟩
    rw [← e1, DV.aPlusQ_eq] at e2
    unfold DV.sigPar at e2
    rw [dif_pos hi] at e2
    have e3 := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at e3
    unfold ext0 kaR
    rw [dif_pos hi']
    exact e3
  rw [big 0 (by omega), big (D.R.k - 2) (by omega)]
  have a1 := (L.cloud_v τ ⟨0, by omega⟩).2
  have a2 := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
  have a3 : (0 : ℝ) ≤ ((D.R.k - 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  push_cast at a1 a2 ⊢
  linarith

def restAt {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.what₂.Tau) : ℝ :=
  (∑ i, (w.aP τ i : ℝ)) + (∑ i, (w.aM τ i : ℝ)) -
    ((D.R.k : ℝ) - 1) * ((ext0 (w.aP τ) (D.R.k - 2) : ℝ) - ext0 (w.aP τ) (D.R.k - 1))

theorem restAt_bounds (hj : InR D j) (τ : D.what₂.Tau) :
    0 ≤ restAt (lR Tp hK j) τ ∧
      (Tp.TO : ℝ) * restAt (lR Tp hK j) τ ≤ D.R.k * (L.Sc + 3 * L.etaSz + 12 * D.R.k) := by
  have h1 := hj.1
  have h2 := hj.2
  have hmk := D.R.m_add_three_le_k
  have hk : 5 ≤ D.R.k := by have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k - 2 + 1 + j := by show D.R.k + j - 1 = _; omega
  have hs2 : (D.R.sigW j).2 = D.R.m - j := rfl
  have hk1 : D.R.k - 1 = D.R.k - 2 + 1 := by omega
  have hkr : (D.R.k : ℝ) - 1 = ((D.R.k - 2 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hA : Antitone fun i => (ext0 ((lR Tp hK j).aP τ) i : ℝ) := fun a b hab =>
    Nat.cast_le.2 (partitionExtendByZero_antitone ((lR Tp hK j).aPlus_antitone τ) hab)
  have hB : Antitone fun i => (ext0 ((lR Tp hK j).aM τ) i : ℝ) := fun a b hab =>
    Nat.cast_le.2 (partitionExtendByZero_antitone ((lR Tp hK j).aM_anti τ) hab)
  obtain ⟨r1, r2⟩ := rest_bounds _ hA (fun i => Nat.cast_nonneg _) (D.R.k - 2) j
  rw [← hs, ← sum_extendByZero_fin_eq_sum_of_eq, ← hkr, ← hk1] at r1 r2
  have m0 : (0 : ℝ) ≤ ∑ i, ((lR Tp hK j).aM τ i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have m1 : ∑ i, ((lR Tp hK j).aM τ i : ℝ) ≤ ((D.R.sigW j).2 : ℝ) * ext0 ((lR Tp hK j).aM τ) 0 := by
    rw [sum_extendByZero_fin_eq_sum_of_eq]
    have := Finset.sum_le_card_nsmul (Finset.range (D.R.sigW j).2) _ _ (fun i _ => hB (Nat.zero_le i))
    rwa [Finset.card_range, nsmul_eq_mul] at this
  obtain ⟨-, w2, w3⟩ := GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj τ
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have t1 := telescope _ _ _ (step Tp.TO _ _ (mul_lGapP_le_gapZ_add_two Tp hK j τ)) 0 (D.R.k - 2)
  have t2 := entry_le Tp.TO _ _ (mul_lGapP_le_gapZ_add_two Tp hK j τ) (D.R.k - 1) (by omega)
  have t3 := entry_le Tp.TO _ _ (gapM_le Tp hK j τ) 0 (Nat.zero_le _)
  have s1 := kappa_spread Tp hK j hj τ
  have s2 : (ext0 ((kaR Tp hK j).aP τ) (D.R.k - 1) : ℝ) ≤ L.etaSz := by
    unfold ext0
    split_ifs with h
    · exact w2 _ le_rfl
    · simpa using he.le
  have s3 : (ext0 ((kaR Tp hK j).aM τ) 0 : ℝ) ≤ L.etaSz := by
    unfold ext0
    split_ifs with h
    · exact w3 _
    · simpa using he.le
  rw [zero_add] at t1
  change (Tp.TO : ℝ) * ((ext0 ((lR Tp hK j).aP τ) 0 : ℝ) - ext0 ((lR Tp hK j).aP τ) (D.R.k - 2)) ≤ _ at t1
  change (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP τ) (D.R.k - 1) : ℝ) ≤ _ at t2
  change (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM τ) 0 : ℝ) ≤ _ at t3
  have c0 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have c1 : ((D.R.k - 2 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast Nat.sub_le _ _
  have c2 : ((D.R.sigW j).1 : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by omega : (D.R.sigW j).1 ≤ 2 * D.R.k)
  have c3 : ((D.R.sigW j).2 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : (D.R.sigW j).2 ≤ D.R.k)
  have c4 : (j : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : j ≤ D.R.k)
  have c5 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have c6 : (0 : ℝ) ≤ ((D.R.sigW j).2 : ℝ) := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ Tp.TO := Nat.cast_nonneg _
  unfold restAt
  refine ⟨by linarith, ?_⟩
  have u1 : ((D.R.k : ℝ) - 1) * ((Tp.TO : ℝ) * ((ext0 ((lR Tp hK j).aP τ) 0 : ℝ) - ext0 ((lR Tp hK j).aP τ) (D.R.k - 2))) ≤
      D.R.k * (L.Sc + 2 * D.R.k) :=
    (mul_le_mul_of_nonneg_left (show _ ≤ L.Sc + 2 * D.R.k by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have u2 : ((D.R.k : ℝ) - 1 + j) * ((Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP τ) (D.R.k - 1) : ℝ)) ≤
      (2 * D.R.k) * (L.etaSz + 4 * D.R.k) :=
    (mul_le_mul_of_nonneg_left (show _ ≤ L.etaSz + 4 * D.R.k by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have u3 : ((D.R.sigW j).2 : ℝ) * ((Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM τ) 0 : ℝ)) ≤
      D.R.k * (L.etaSz + 2 * D.R.k) :=
    (mul_le_mul_of_nonneg_left (show _ ≤ L.etaSz + 2 * D.R.k by linarith) c6).trans
      (mul_le_mul_of_nonneg_right c3 (by linarith))
  have v1 := mul_le_mul_of_nonneg_left r2 hT
  have v2 := mul_le_mul_of_nonneg_left m1 hT
  nlinarith

theorem le_two_floor {x : ℝ} (h : 1 ≤ x) : 1 ≤ (⌊x⌋₊ : ℝ) ∧ x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h)
  have h2 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have h3 := Nat.lt_floor_add_one x
  exact ⟨h2, by linarith⟩

include Tp in
theorem sizes_le : L.Sc ≤ 2 * (numOf D L).Sc ∧ L.etaSz ≤ 2 * (numOf D L).eta ∧ (D.R.k : ℝ) ≤ (numOf D L).Sc := by
  have hT : (1 : ℝ) ≤ Tp.TO := by exact_mod_cast TO_pos Tp
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hm : (0 : ℝ) < D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 0 < D.R.m)
  obtain ⟨d1, d2⟩ := le_two_floor (x := ((D.s.Del : ℚ) : ℝ)) (by have := Tp.Del_TO; nlinarith)
  obtain ⟨-, e2⟩ := le_two_floor (x := LevelStarExponents.h0 L) (by have := Tp.heightBound_ge_order_sq; nlinarith)
  have e3 : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
  have x1 : (numOf D L).Sc = D.R.k * (4 * (⌊((D.s.Del : ℚ) : ℝ)⌋₊ : ℝ)) := rfl
  have x2 : (numOf D L).eta = D.R.m * (⌊LevelStarExponents.h0 L⌋₊ : ℝ) := rfl
  rw [x1, x2, L.Sc_eq]
  refine ⟨by nlinarith, ?_, by nlinarith⟩
  rw [e3]
  nlinarith

end Place

theorem rest_degree_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), T.Q.Pins → ∀ j : ℕ, InR D j →
  0 ≤ restOf (numOf D L) (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) ∧
  (Tp.TO : ℝ) * restOf (numOf D L) (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) ≤ 100 * (D.R.f * D.R.k * ((numOf D L).Sc + (numOf D L).eta)) := by
  intro D L Pm Tp hK T hp j hj
  obtain ⟨hD, -, -, -, hw⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hp j hj (lR Tp hK j)
  obtain ⟨hb, hc⟩ := plOf_bijective_card D
  have key : restOf (numOf D L) (T.Q.Dw j) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) =
      ∑ τ, restAt (lR Tp hK j) τ := by
    have e1 : (∑ z : RPl D.R, (gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z : ℝ)) =
        ∑ τ, ((ext0 ((lR Tp hK j).aP τ) (D.R.k - 2) : ℝ) - ext0 ((lR Tp hK j).aP τ) (D.R.k - 1)) := by
      refine Fintype.sum_bijective _ hb _ _ fun z => ?_
      show ((wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) -
        wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) : ℕ) : ℝ) = _
      rw [(hw _ _).1, (hw _ _).1, Nat.cast_sub (partitionExtendByZero_antitone ((lR Tp hK j).aPlus_antitone _) (by omega))]
    unfold restOf restAt
    rw [hD, Finset.sum_sub_distrib, ← Finset.mul_sum, ← e1]
    unfold WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    rfl
  rw [key, Finset.mul_sum]
  refine ⟨Finset.sum_nonneg fun τ _ => (restAt_bounds Tp hK j hj τ).1, ?_⟩
  have h1 := Finset.sum_le_card_nsmul Finset.univ _ _ (fun τ _ => (restAt_bounds Tp hK j hj τ).2)
  rw [Finset.card_univ, hc, nsmul_eq_mul] at h1
  obtain ⟨s1, s2, s3⟩ := sizes_le Tp
  have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have he := L.etaSz_pos
  have h2 : L.Sc + 3 * L.etaSz + 12 * D.R.k ≤ 100 * ((numOf D L).Sc + (numOf D L).eta) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.k)
  linarith

end GlobalTheory.RestDegree
