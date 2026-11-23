import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.BlockDiagonalMulVecApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.T8m

set_option autoImplicit false

noncomputable section

open NumberField Matrix Module MeasureTheory
open scoped ComplexOrder Classical

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

def t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    Matrix (Fin I.n) (Fin j) ℂ :=
  (uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * (Matrix.of fun i k => b k i).map (I.φ v)

theorem coord_linear_comb (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (a : Fin j → I.E) :
    coordV I x v (∑ k, a k • b k) = t8C I x v b *ᵥ fun k => I.φ v (a k) := by
  unfold coordV t8C
  have hw : (fun i => I.φ v ((∑ k, a k • b k) i)) =
      (Matrix.of fun i k => b k i).map (I.φ v) *ᵥ fun k => I.φ v (a k) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, map_sum, mul_comm]
  rw [hw, Matrix.mulVec_mulVec]

theorem gramV_eq_conjTranspose_t8C_mul_t8C (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ} (b : Fin j → Fin I.n → I.E) :
    gramV I x v b = (t8C I x v b)ᴴ * t8C I x v b := by
  have hc : ∀ a i, coordV I x v (b a) i = t8C I x v b i a := by
    intro a i
    first
      | rfl
      | (unfold coordV t8C; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply])
  unfold gramV
  ext a c
  simp only [hc, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem coord_matrix_mulVec_injective (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) :
    Function.Injective (t8C I x v b).mulVec := by
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  intro w w' h
  apply mulVec_injective_map (I.φ v) Bm hB
  apply Matrix.mulVec_injective_iff_isUnit.2 hAu
  simpa only [t8C, Matrix.mulVec_mulVec] using h

def linearCombinationOfRows {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) : (Fin j → E) →+ (Fin n → E) where
  toFun a := ∑ k, a k • b k
  map_zero' := by simp
  map_add' a a' := by simp [add_smul, Finset.sum_add_distrib]

theorem linearComb_apply {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (a : Fin j → E) :
    linearCombinationOfRows b a = ∑ k, a k • b k := rfl

theorem linear_comb_injective {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (hb : LinearIndependent E b) :
    Function.Injective (linearCombinationOfRows b) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  rw [linearComb_apply] at ha
  funext k
  exact Fintype.linearIndependent_iff.mp hb a ha k

theorem linearComb_single {n j : ℕ} {E : Type} [Field E] (b : Fin j → Fin n → E) (k : Fin j) (c : E) :
    linearCombinationOfRows b (Pi.single k c) = c • b k := by
  rw [linearComb_apply]
  simp [Pi.single_apply, ite_smul]

theorem short_vector_sublattice (I : AutInst) (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (x : I.GA) (s : Sub I x) (C : ℝ)
    (hC : ∀ (L : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) [DiscreteTopology L] [IsZLattice ℝ L],
      ∃ u ∈ L, u ≠ 0 ∧ ‖u‖ ^ 2 ≤ C * ZLattice.covolume L ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ))) :
    ∃ u ∈ s.B, u ≠ 0 ∧ ∑ v, ∑ i, ‖coordV I x v u i‖ ^ 2 ≤
      C * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) * size I s ^ 2 := by

  choose R hR hRdet using fun v => gram_factor_invertible (t8C I x v s.b) (coord_matrix_mulVec_injective I x v s.b s.b_ind)
  have hgram : ∀ v, (gramV I x v s.b).det.re = Complex.normSq (R v).det := by
    intro v
    rw [gramV_eq_conjTranspose_t8C_mul_t8C, hR v, Matrix.det_mul, Matrix.det_conjTranspose,
      ← Complex.ofReal_re (Complex.normSq (R v).det), Complex.normSq_eq_conj_mul_self]
    rfl

  set P : Submodule (𝓞 I.E) (Fin I.n → I.E) := Submodule.span (𝓞 I.E) (Set.range s.b) with hP
  have hfin : Finite (s.B ⧸ P.comap s.B.subtype) := by
    obtain ⟨M, hMfg, hM⟩ := h1 I x
    refine h2 I.E I.n s.j M s.B s.b hMfg ?_ s.b_ind s.b_mem s.B_span
    intro u hu
    rw [← SetLike.mem_coe, hM]
    exact s.B_lat hu
  set N : ℕ := Nat.card (s.B ⧸ P.comap s.B.subtype) with hN
  have hN0 : 0 < N := Nat.card_pos

  set lin := linearCombinationOfRows s.b with hlin
  have hlinj : Function.Injective lin := linear_comb_injective s.b s.b_ind
  set Bp : AddSubgroup (Fin s.j → I.E) := s.B.toAddSubgroup.comap lin with hBp
  set Op : AddSubgroup (Fin s.j → I.E) := (t8O I s.j).toAddSubgroup with hOp
  have hgen : ∀ p : Σ _ : Fin s.j, Free.ChooseBasisIndex ℤ (𝓞 I.E),
      lin (Pi.single p.1 (integralBasis I.E p.2)) = (RingOfIntegers.basis I.E p.2) • s.b p.1 := by
    intro p
    rw [hlin, linearComb_single, integralBasis_apply, algebraMap_smul]
  have hOB : Op ≤ Bp := by
    intro y hy
    change lin y ∈ s.B
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      rw [hgen]
      exact s.B.smul_mem _ (s.b_mem p.1)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact s.B.add_mem hy hz
    | smul c y _ hy => rw [map_zsmul]; exact s.B.toAddSubgroup.zsmul_mem hy c
  have hmapO : Op.map lin = P.toAddSubgroup := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      change lin a ∈ P
      induction ha using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        rw [hgen]
        exact P.smul_mem _ (Submodule.subset_span ⟨p.1, rfl⟩)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add]; exact P.add_mem hy hz
      | smul c y _ hy => rw [map_zsmul]; exact P.toAddSubgroup.zsmul_mem hy c
    · intro hy
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 I.E)).1 (show y ∈ P from hy)
      refine ⟨fun k => (c k : I.E), mem_integral_vectors I s.j _ fun k => ⟨c k, rfl⟩, ?_⟩
      rw [hlin, linearComb_apply, ← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact algebraMap_smul I.E (c k) (s.b k)
  have hmapB : Bp.map lin = s.B.toAddSubgroup := by
    refine AddSubgroup.map_comap_eq_self ?_
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (s.B_span hu)
    exact ⟨c, hc⟩
  have hrel : Op.relIndex Bp = N := by
    rw [← AddSubgroup.relIndex_map_map_of_injective Op Bp hlinj, hmapO, hmapB, hN]
    rfl

  have hRdet' : ∀ v, (R v).det ≠ 0 := hRdet
  set Θ := t8Th R with hΘ
  have hΘinj : Function.Injective Θ := blockTransform_injective R hRdet'
  set L₁ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    Submodule.span ℤ (Set.range (blockBasis R hRdet')) with hL₁
  set L₂ : Submodule ℤ (EuclideanSpace ℝ (Fin (2 * I.f * s.j))) :=
    (Bp.map Θ).toIntSubmodule with hL₂
  have hL₁' : L₁.toAddSubgroup = Op.map Θ := by
    rw [hL₁, ← map_integral_vectors_span R hRdet']
    rfl
  have hL₂' : L₂.toAddSubgroup = Bp.map Θ := AddSubgroup.toIntSubmodule_toAddSubgroup _
  have h12 : L₁ ≤ L₂ := by
    intro y hy
    have hy' : y ∈ L₁.toAddSubgroup := hy
    rw [hL₁'] at hy'
    show y ∈ L₂.toAddSubgroup
    rw [hL₂']
    exact AddSubgroup.map_mono hOB hy'
  have hrel2 : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup = N := by
    rw [hL₁', hL₂', AddSubgroup.relIndex_map_map_of_injective Op Bp hΘinj, hrel]

  have hNR : ((N : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN0.ne')
  set β' := (blockBasis R hRdet').isUnitSMul (w := fun _ => ((N : ℝ))⁻¹) (fun _ => isUnit_iff_ne_zero.2 hNR)
    with hβ'
  have hsub : (L₂ : Set (EuclideanSpace ℝ (Fin (2 * I.f * s.j)))) ⊆ Submodule.span ℤ (Set.range β') := by
    intro w hw
    have hw' : w ∈ L₂.toAddSubgroup := hw
    rw [hL₂'] at hw'
    obtain ⟨a, ha, rfl⟩ := hw'
    have hNa : N • a ∈ Op := by
      rw [← hrel]
      exact AddSubgroup.nsmul_relIndex_mem Op ha
    have hNw : N • Θ a ∈ L₁ := by
      have : Θ (N • a) ∈ L₁.toAddSubgroup := by
        rw [hL₁']
        exact ⟨N • a, hNa, rfl⟩
      rwa [map_nsmul] at this
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hNw
    refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
    simp only [hβ', Basis.isUnitSMul_apply]
    have e : ∀ p, c p • ((N : ℝ)⁻¹ • blockBasis R hRdet' p) = (N : ℝ)⁻¹ • (c p • blockBasis R hRdet' p) :=
      fun p => smul_comm _ _ _
    simp only [e, ← Finset.smul_sum, hc]
    rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN0.ne')]
  have : DiscreteTopology L₂ :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range β'))) hsub
  have : IsZLattice ℝ L₂ := ⟨by
    rw [eq_top_iff, ← (blockBasis R hRdet').span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, rfl⟩
    exact h12 (Submodule.subset_span ⟨p, rfl⟩)⟩

  have hcov := ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h12
  rw [hrel2, covolume_blockBasis] at hcov
  have hht : ht I s = (∏ v, Complex.normSq (R v).det) / N := by
    rw [ht]
    simp only [hgram]
    rfl
  have hcov2 : ZLattice.covolume L₂ = t8K I s.j * ht I s := by
    have hpos := ZLattice.covolume_pos L₂ volume
    rw [hht]
    rw [div_eq_iff hpos.ne'] at hcov
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN0
    field_simp
    linarith
  have hht0 : 0 ≤ ht I s := by
    rw [hht]
    exact div_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

  obtain ⟨w, hw, hw0, hwb⟩ := hC L₂
  have hw' : w ∈ L₂.toAddSubgroup := hw
  rw [hL₂'] at hw'
  obtain ⟨a, ha, rfl⟩ := hw'
  refine ⟨lin a, ha, ?_, ?_⟩
  · intro h0
    apply hw0
    have : a = 0 := hlinj (by rw [h0, map_zero])
    rw [this, map_zero]
  · have hnorm : ‖Θ a‖ ^ 2 = ∑ v, ∑ i, ‖coordV I x v (lin a) i‖ ^ 2 := by
      rw [hΘ, blockTransform_norm_sq]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hlin, linearComb_apply, coord_linear_comb]
      exact (norm_sq_eq_of_gram_eq _ _ (hR v) _).symm
    rw [← hnorm]
    refine hwb.trans (le_of_eq ?_)
    rw [hcov2, Real.mul_rpow (integral_covolume_pos I s.j).le hht0, size, ← Real.rpow_mul_natCast hht0]
    have hf : (0 : ℝ) < I.f := by
      have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
      rw [card_infinite_places] at this
      exact_mod_cast this
    have hj : (0 : ℝ) < s.j := by exact_mod_cast s.j_pos
    have e : (1 : ℝ) / (2 * (I.f : ℝ) * (s.j : ℝ)) * ((2 : ℕ) : ℝ) = (2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [e]
    ring

theorem minkowski_submodule_short_vector (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) (h8m : MinkowskiFirstTheorem) : MinkowskiSubmodule := by
  intro I
  let cj : ℕ → ℝ := fun j =>
    if h : 1 ≤ 2 * I.f * j then (h8m _ h).choose * t8K I j ^ ((2 : ℝ) / ((2 * I.f * j : ℕ) : ℝ)) else 0
  have hcj : ∀ j, 0 ≤ cj j := by
    intro j
    simp only [cj]
    split_ifs with h
    · exact mul_nonneg (h8m _ h).choose_spec.1.le (Real.rpow_nonneg (integral_covolume_pos I j).le _)
    · exact le_rfl
  refine ⟨1 + ∑ j ∈ Finset.range (I.n + 1), cj j, by
    have := Finset.sum_nonneg fun j (_ : j ∈ Finset.range (I.n + 1)) => hcj j
    linarith, ?_⟩
  intro x s
  have hd : 1 ≤ 2 * I.f * s.j := by
    have : 0 < Fintype.card (InfinitePlace I.F) := Fintype.card_pos
    rw [card_infinite_places] at this
    have := s.j_pos
    have : 1 ≤ I.f * s.j := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [Nat.mul_assoc]
    omega
  obtain ⟨u, hu, hu0, hub⟩ := short_vector_sublattice I h1 h2 x s (h8m _ hd).choose (fun L _ _ => (h8m _ hd).choose_spec.2 L)
  refine ⟨u, hu, hu0, hub.trans ?_⟩
  have hjn : s.j ≤ I.n := by
    have := s.b_ind.fintype_card_le_finrank
    simpa using this
  have hle : cj s.j ≤ 1 + ∑ j ∈ Finset.range (I.n + 1), cj j := by
    have := Finset.single_le_sum (f := cj) (fun j _ => hcj j) (Finset.mem_range.2 (Nat.lt_succ_of_le hjn))
    linarith
  have hcs : cj s.j = (h8m _ hd).choose * t8K I s.j ^ ((2 : ℝ) / ((2 * I.f * s.j : ℕ) : ℝ)) := by
    simp only [cj, dif_pos hd]
  rw [← hcs]
  exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

end Formalism.L2.SG.Pf.Tau
