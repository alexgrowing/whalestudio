import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar

open Module Submodule

noncomputable section

namespace Formalism.HN

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem duality_mem_dualZ (L : Submodule ℤ E) (y : E) :
    y ∈ dualZ L ↔ y ∈ span ℝ (L : Set E) ∧ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  have key : ∀ x : E, y ∈ ((Int.castAddHom ℝ).range.toIntSubmodule).comap
      ((innerSL ℝ x : E →L[ℝ] ℝ).toLinearMap.restrictScalars ℤ) ↔
        ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
    intro x
    rw [Submodule.mem_comap]
    change (innerSL ℝ x) y ∈ (Int.castAddHom ℝ).range ↔ _
    rw [AddMonoidHom.mem_range]
    simp
  simp only [dualZ, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_iInf, key]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem duality_inner_sum_dual (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) (c : ι → ℝ) (k : ι) :
    inner ℝ (v k) (∑ i, c i • w i) = c k := by
  simp [inner_sum, real_inner_smul_right, hvw]

theorem duality_eq_zero_of_inner (v : ι → E) {z : E} (hz : z ∈ span ℝ (Set.range v))
    (h : ∀ k, inner ℝ (v k) z = 0) : z = 0 := by
  have hall : ∀ u ∈ span ℝ (Set.range v), inner ℝ u z = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact h k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul a x _ hx => rw [real_inner_smul_left, hx, mul_zero]
  have hzz := hall z hz
  exact inner_self_eq_zero.mp hzz

theorem duality_expand (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) {y : E}
    (hy : y ∈ span ℝ (Set.range v)) : y = ∑ k, inner ℝ (v k) y • w k := by
  have hs : (∑ k, inner ℝ (v k) y • w k) ∈ span ℝ (Set.range v) :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hw k)
  have h0 := duality_eq_zero_of_inner v (Submodule.sub_mem _ hy hs) fun j => by
    have h2 := duality_inner_sum_dual v w hvw (fun k => inner ℝ (v k) y) j
    rw [inner_sub_right, sub_eq_zero]
    exact h2.symm
  exact sub_eq_zero.mp h0

private theorem exists_int_inner_of_mem_span_int (v : ι → E) (y : E)
    (hy : ∀ k, ∃ n : ℤ, (n : ℝ) = inner ℝ (v k) y) {x : E} (hx : x ∈ span ℤ (Set.range v)) :
    ∃ n : ℤ, (n : ℝ) = inner ℝ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hy k
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [inner_add_left, ← ha, ← hb, Int.cast_add]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    have hsm : a • x = (a : ℝ) • x := by
      exact (Int.cast_smul_eq_zsmul (R := ℝ) a x).symm
    rw [hsm, real_inner_smul_left, ← hb, Int.cast_mul]

theorem duality_dualZ_span (v w : ι → E) (hw : ∀ i, w i ∈ span ℝ (Set.range v))
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) :
    dualZ (span ℤ (Set.range v)) = span ℤ (Set.range w) := by
  have hspan : span ℝ ((span ℤ (Set.range v) : Submodule ℤ E) : Set E) = span ℝ (Set.range v) := by
    exact Submodule.span_span_of_tower ℤ ℝ (Set.range v)
  apply le_antisymm
  · intro y hy
    rw [duality_mem_dualZ, hspan] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [duality_expand v w hw hvw hy1]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨n, hn⟩ := hy2 (v k) (Submodule.subset_span (Set.mem_range_self k))
    have hsm : inner ℝ (v k) y • w k = n • w k := by
      rw [← hn]
      exact Int.cast_smul_eq_zsmul (R := ℝ) n (w k)
    rw [hsm]
    exact Submodule.smul_mem _ n (Submodule.subset_span (Set.mem_range_self k))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, duality_mem_dualZ, hspan]
    refine ⟨hw i, fun x hx => exists_int_inner_of_mem_span_int v (w i) (fun k => ?_) hx⟩
    refine ⟨if k = i then 1 else 0, ?_⟩
    rw [hvw]
    split_ifs <;> simp

theorem duality_linIndep (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) : LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  rw [← duality_inner_sum_dual v w hvw g k, hg, inner_zero_right]

theorem duality_exists_dual (v : ι → E) (hv : LinearIndependent ℝ v) :
    ∃ w : ι → E, (∀ i, w i ∈ span ℝ (Set.range v)) ∧
      (∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) ∧
      (Matrix.gram ℝ w).det = ((Matrix.gram ℝ v).det)⁻¹ := by
  have hGdet : (Matrix.gram ℝ v).det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    have hz : ∑ i, c i • v i = 0 := by
      refine duality_eq_zero_of_inner v
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span (Set.mem_range_self i))) fun k => ?_
      have hk : ∑ i, Matrix.gram ℝ v k i * c i = 0 := congrFun hc k
      rw [inner_sum, ← hk]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
    funext i
    exact Fintype.linearIndependent_iff.mp hv c hz i
  have hunit : IsUnit (Matrix.gram ℝ v).det := isUnit_iff_ne_zero.mpr hGdet
  have hmul : Matrix.gram ℝ v * (Matrix.gram ℝ v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have hmul' : (Matrix.gram ℝ v)⁻¹ * Matrix.gram ℝ v = 1 := Matrix.nonsing_inv_mul _ hunit
  refine ⟨fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j,
    fun i => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)), fun k i => ?_, ?_⟩
  · show inner ℝ (v k) (∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j) = if k = i then 1 else 0
    have h := congrFun (congrFun hmul k) i
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [inner_sum, ← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, Matrix.gram_apply, mul_comm]
  · show (Matrix.gram ℝ (fun i => ∑ j, (Matrix.gram ℝ v)⁻¹ j i • v j)).det = _
    rw [Formalism.F.gram_sum_smul_eq_transpose_mul v (Matrix.gram ℝ v)⁻¹, Matrix.det_mul,
      Matrix.det_mul, Matrix.det_transpose]
    have h1 : ((Matrix.gram ℝ v)⁻¹).det * (Matrix.gram ℝ v).det = 1 := by
      rw [← Matrix.det_mul, hmul', Matrix.det_one]
    rw [h1, one_mul]
    exact eq_inv_of_mul_eq_one_left h1

variable [FiniteDimensional ℝ E]

private theorem rk_span_range_eq_card_of_linearIndependent (u : ι → E) (hu : LinearIndependent ℝ u) :
    Formalism.F.rk (span ℤ (Set.range u)) = Fintype.card ι := by
  have := (Formalism.F.discreteTopology_span_range_and_covol u hu).1
  rw [Formalism.F.rank_eq_finrank_span (span ℤ (Set.range u)), Submodule.span_span_of_tower,
    finrank_span_eq_card hu]

theorem duality_basic (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (dualZ L) ∧ Formalism.F.rk (dualZ L) = Formalism.F.rk L ∧
    Formalism.F.deg (dualZ L) = - Formalism.F.deg L ∧ dualZ (dualZ L) = L := by
  obtain ⟨v, hv, hL⟩ : ∃ v : Fin (Module.finrank ℤ L) → E,
      LinearIndependent ℝ v ∧ span ℤ (Set.range v) = L :=
    ⟨fun i => ((Module.finBasis ℤ L i : L) : E),
      Formalism.F.linearIndependent_coe_basis L (Module.finBasis ℤ L),
      Formalism.F.span_range_coe_basis' L (Module.finBasis ℤ L)⟩
  obtain ⟨w, hw, hvw, hdet⟩ := duality_exists_dual v hv
  have hwli := duality_linIndep v w hvw
  have hdual : dualZ L = span ℤ (Set.range w) := by
    rw [← duality_dualZ_span v w hw hvw, hL]
  have hwv : ∀ k i, inner ℝ (w k) (v i) = if k = i then 1 else 0 := by
    intro k i
    rw [real_inner_comm, hvw]
    by_cases h : k = i
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hv' : ∀ i, v i ∈ span ℝ (Set.range w) := by
    intro i
    rw [duality_expand v w hw hvw (Submodule.subset_span (Set.mem_range_self i))]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self k))
  have hrkL := rk_span_range_eq_card_of_linearIndependent v hv
  rw [hL] at hrkL
  have hcv := (Formalism.F.discreteTopology_span_range_and_covol v hv).2
  rw [hL] at hcv
  have hcw := Formalism.F.discreteTopology_span_range_and_covol w hwli
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdual]
    exact hcw.1
  · rw [hdual, rk_span_range_eq_card_of_linearIndependent w hwli, hrkL]
  · rw [hdual]
    unfold Formalism.F.deg
    rw [hcw.2, hcv, hdet, Real.sqrt_inv, Real.log_inv]
  · rw [hdual, duality_dualZ_span w v hv' hwv, hL]

theorem duality_ne_bot (L : Submodule ℤ E) [DiscreteTopology L] (hL : L ≠ ⊥) : dualZ L ≠ ⊥ := by
  intro h
  have h1 := (duality_basic L).2.1
  have h2 := Formalism.F.att_rk_pos hL
  rw [h] at h1
  have h3 : Formalism.F.rk (⊥ : Submodule ℤ E) = 0 := by
    simp [Formalism.F.rk]
  omega

private theorem starProjection_mem_and_sub_mem_orthogonal (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x ∈ K ∧ x - K.starProjection x ∈ Kᗮ := by
  constructor
  · exact K.starProjection_apply_mem x
  · exact K.sub_starProjection_mem_orthogonal x

theorem duality_dualZ_quot_le (L T : Submodule ℤ E) (hT : T ≤ L) :
    dualZ (Formalism.F.quot L T) ≤ dualZ L := by
  intro y hy
  rw [duality_mem_dualZ] at hy ⊢
  obtain ⟨hy1, hy2⟩ := hy
  have hWL : span ℝ (T : Set E) ≤ span ℝ (L : Set E) := Submodule.span_mono hT
  have hQ : ∀ x ∈ L, (span ℝ (T : Set E))ᗮ.starProjection x ∈ Formalism.F.quot L T ∧
      (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ∧
      x - (span ℝ (T : Set E))ᗮ.starProjection x ∈ span ℝ (T : Set E) := by
    intro x hx
    obtain ⟨h1, h2⟩ := starProjection_mem_and_sub_mem_orthogonal (span ℝ (T : Set E))ᗮ x
    refine ⟨Submodule.mem_map_of_mem
      (f := ((span ℝ (T : Set E))ᗮ.starProjection : E →L[ℝ] E).toLinearMap.restrictScalars ℤ) hx,
      h1, ?_⟩
    rwa [Submodule.orthogonal_orthogonal] at h2
  have hspan : span ℝ (Formalism.F.quot L T : Set E) ≤
      (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E) := by
    refine Submodule.span_le.mpr fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := hq
    change (span ℝ (T : Set E))ᗮ.starProjection x ∈ (span ℝ (T : Set E))ᗮ ⊓ span ℝ (L : Set E)
    obtain ⟨-, h1, h2⟩ := hQ x hx
    rw [Submodule.mem_inf]
    refine ⟨h1, ?_⟩
    have h4 := Submodule.sub_mem _ (Submodule.subset_span hx : x ∈ span ℝ (L : Set E)) (hWL h2)
    rwa [sub_sub_cancel] at h4
  obtain ⟨hyW, hyL⟩ := Submodule.mem_inf.mp (hspan hy1)
  refine ⟨hyL, fun x hx => ?_⟩
  obtain ⟨hq, -, h2⟩ := hQ x hx
  obtain ⟨n, hn⟩ := hy2 _ hq
  refine ⟨n, ?_⟩
  have h0 : inner ℝ (x - (span ℝ (T : Set E))ᗮ.starProjection x) y = 0 := by
    exact Submodule.inner_right_of_mem_orthogonal h2 hyW
  rw [inner_sub_left, sub_eq_zero] at h0
  rw [hn, h0]

private theorem discreteTopology_of_le_of_discreteTopology {L N : Submodule ℤ E} (h : N ≤ L)
    [DiscreteTopology L] : DiscreteTopology N := by
  exact Formalism.F.discreteTopology_of_le h

theorem duality_compl (L S : Submodule ℤ E) [hL : DiscreteTopology L] (hS : S ≤ L) :
    ∃ N : Submodule ℤ E, N ≤ dualZ L ∧ Formalism.F.rk N + Formalism.F.rk S = Formalism.F.rk L ∧
      Formalism.F.deg S - Formalism.F.deg L ≤ Formalism.F.deg N := by
  obtain ⟨hsat, hSS, hrkS⟩ := Formalism.F.saturProps E L S hL hS
  obtain ⟨hQd, hrk, hdeg⟩ :=
    Formalism.F.degQuot E L (Formalism.F.satur L S) hL hsat
  have := hQd
  obtain ⟨-, hr, hd, -⟩ :=
    duality_basic (Formalism.F.quot L (Formalism.F.satur L S))
  have hS'd : DiscreteTopology (Formalism.F.satur L S) :=
    discreteTopology_of_le_of_discreteTopology hsat.1
  have hcov := Formalism.F.covolAntiSameRank E S (Formalism.F.satur L S) hS'd
    hSS hrkS.symm
  have hpos := Formalism.F.covol_pos (Formalism.F.satur L S)
  refine ⟨_, duality_dualZ_quot_le L _ hsat.1, ?_, ?_⟩
  · rw [hr, ← hrkS]
    omega
  · rw [hd]
    have hdS : Formalism.F.deg S ≤
        Formalism.F.deg (Formalism.F.satur L S) := by
      unfold Formalism.F.deg
      exact neg_le_neg (Real.log_le_log hpos hcov)
    linarith

theorem duality_zl_id (N : Submodule ℤ E) : zl (AddMonoidHom.id E) N = N := by
  ext y
  rw [satR_mem_zl]
  simp

end Dual

universe u

theorem duality_muMax (h1 : MuChar.{0, u, u}) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    (hL : L ≠ ⊥) :
    muMax (AddMonoidHom.id E) (dualZ L) = - muMin (AddMonoidHom.id E) L := by
  obtain ⟨hDd, hDr, hDdeg, hDD⟩ := duality_basic L
  have hD0 := duality_ne_bot L hL
  have hlat : ∀ M : Submodule ℤ E, DiscreteTopology M → IsLat (AddMonoidHom.id E) M := by
    intro M hM
    unfold IsLat
    refine ⟨fun x _ y _ h => by simpa using h, ?_⟩
    rw [duality_zl_id]
    exact hM
  have hA := (h1 ℤ E E (AddMonoidHom.id E) (dualZ L) (hlat _ hDd) hD0).1
  have hB := (h1 ℤ E E (AddMonoidHom.id E) L (hlat _ inferInstance) hL).2.1
  have key : ∀ θ : ℝ, muMax (AddMonoidHom.id E) (dualZ L) ≤ θ ↔
      -θ ≤ muMin (AddMonoidHom.id E) L := by
    intro θ
    rw [hA θ, hB (-θ)]
    simp only [deg, rk, duality_zl_id]
    have := hDd
    constructor
    · intro h N hN
      obtain ⟨M, hM, hr, hd⟩ := duality_compl L N hN
      have hMd := h M hM
      have hr' : (Formalism.F.rk M : ℝ) + Formalism.F.rk N = Formalism.F.rk L := by
        exact_mod_cast hr
      have hc : (Formalism.F.rk M : ℝ) = Formalism.F.rk L - Formalism.F.rk N := by
        linarith
      rw [hc] at hMd
      rw [neg_mul]
      linarith
    · intro h M hM
      obtain ⟨N, hN, hr, hd⟩ := duality_compl (dualZ L) M hM
      rw [hDD] at hN
      have hNd := h N hN
      have hr' : (Formalism.F.rk N : ℝ) + Formalism.F.rk M = Formalism.F.rk L := by
        rw [← hDr]
        exact_mod_cast hr
      have hc : (Formalism.F.rk M : ℝ) = Formalism.F.rk L - Formalism.F.rk N := by
        linarith
      rw [hc]
      rw [neg_mul] at hNd
      linarith
  apply le_antisymm
  · exact (key _).mpr (neg_neg _).le
  · have h2 := (key _).mp le_rfl
    linarith

theorem duality_of (h1 : MuChar.{0, u, u}) : Duality.{u} := by
  intro E _ _ _ L hL
  have := hL
  obtain ⟨hDd, hDr, hDdeg, hDD⟩ := duality_basic L
  refine ⟨hDd, hDr, hDdeg, hDD, fun hL0 => ⟨duality_muMax h1 L hL0, ?_⟩⟩
  have := hDd
  have h := duality_muMax h1 (dualZ L)
    (duality_ne_bot L hL0)
  rw [hDD] at h
  linarith

theorem slope_duality_formula : Duality :=
  duality_of slope_characterization

end Formalism.HN
