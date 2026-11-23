import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TwistedScalarSection

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

theorem tsb_mR_cont (n : ℕ) : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_lower_left_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_lower_right_block_alt (n : ℕ) : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.toBlocks₂₂, Matrix.of_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem continuous_first_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_lower_left_block_alt n).const_smul Complex.I).add (continuous_lower_right_block_alt n)

theorem continuous_second_cayley_block (n : ℕ) : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact (((continuous_lower_left_block_alt n).const_smul Complex.I).neg).add (continuous_lower_right_block_alt n)

theorem continuousAt_twisted_section {n : ℕ} (p q : ℕ) (e : ℤ) (M : M2 n) (h0 : M.det ≠ 0) (h1 : (u1 M).det ≠ 0)
    (h2 : (u2 M).det ≠ 0) : ContinuousAt (twistedScalarSection p q e) M := by
  unfold twistedScalarSection f0
  refine ContinuousAt.mul (ContinuousAt.zpow₀ (continuous_id.matrix_det).continuousAt e (Or.inl h0))
    (ContinuousAt.mul ?_ ?_)
  · exact ContinuousAt.zpow₀ ((continuous_first_cayley_block n).matrix_det).continuousAt _ (Or.inl h1)
  · exact ContinuousAt.zpow₀ ((continuous_second_cayley_block n).matrix_det).continuousAt _ (Or.inl h2)

theorem tsb_det_ne (n : ℕ) (g : GR n) : (mR g).det ≠ 0 := by
  have h := g.1.isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp h |>.ne_zero

theorem continuous_spherical_section (hD : CayleyBlocksInvertible) (n p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have : (F0 p q e : GR n → ℂ) = twistedScalarSection p q e ∘ mR := rfl
  rw [this]
  exact (continuousAt_twisted_section p q e (mR g) (tsb_det_ne n g) (hD n g).1 (hD n g).2).comp (tsb_mR_cont n).continuousAt

def kSet (n : ℕ) : Set (M2 n) := (Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ : Set (M2 n)) ∩ {M | InG M}

theorem tsb_kSet_compact (n : ℕ) : IsCompact (kSet n) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n ⊕ Fin n => Set.pi Set.univ fun _ : Fin n ⊕ Fin n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset hK (IsClosed.inter isClosed_unitary ?_) ?_
  · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  · intro U hU
    exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
      mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU.1 i j)

theorem tsb_kSet_mem {n : ℕ} {M : M2 n} (h : M ∈ kSet n) : Mᴴ * M = 1 ∧ M * Mᴴ = 1 ∧ InG M := by
  have hu : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := h.1
  have h1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 := (Matrix.mem_unitaryGroup_iff).1 hu
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using h1, by simpa [Matrix.star_eq_conjTranspose] using h2, h.2⟩

def kOf (n : ℕ) (M : kSet n) : KR n :=
  ⟨⟨⟨M.1, M.1ᴴ, (tsb_kSet_mem M.2).2.1, (tsb_kSet_mem M.2).1⟩, (tsb_kSet_mem M.2).2.2⟩,
    ⟨(tsb_kSet_mem M.2).2.2, (tsb_kSet_mem M.2).1⟩⟩

theorem tsb_kOf_cont (n : ℕ) : Continuous (kOf n) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  exact continuous_subtype_val.matrix_conjTranspose

theorem tsb_kOf_surj (n : ℕ) : Function.Surjective (kOf n) := by
  intro k
  have hk := k.2
  have hM : mR (k : GR n) ∈ kSet n := by
    refine ⟨?_, hk.1⟩
    show mR (k : GR n) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
    rw [Matrix.mem_unitaryGroup_iff']
    simpa [Matrix.star_eq_conjTranspose] using hk.2
  refine ⟨⟨mR (k : GR n), hM⟩, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Units.ext
  rfl

theorem tsb_compact (n : ℕ) : CompactSpace (KR n) := by
  have : CompactSpace (kSet n) := isCompact_iff_compactSpace.mp (tsb_kSet_compact n)
  exact ⟨by rw [← (tsb_kOf_surj n).range_eq]; exact isCompact_range (tsb_kOf_cont n)⟩

def dM {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : M2 n :=
  fromBlocks (diagonal fun j => (Real.exp (t * X j) : ℂ)) 0 0 (diagonal fun j => (Real.exp (-(t * X j)) : ℂ))

theorem exp_diagonal_mul_inverse {n : ℕ} (X : Fin n → ℝ) (t : ℝ) :
    (diagonal fun j => (Real.exp (t * X j) : ℂ)) * (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) = 1 ∧
    (diagonal fun j => (Real.exp (-(t * X j)) : ℂ)) * (diagonal fun j => (Real.exp (t * X j) : ℂ)) = 1 := by
  constructor <;>
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp

theorem tsb_dM_mul {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : dM X t * dM X (-t) = 1 := by
  unfold dM
  rw [fromBlocks_multiply]
  have h := exp_diagonal_mul_inverse X t
  have e1 : (fun j => (Real.exp (-t * X j) : ℂ)) = fun j => (Real.exp (-(t * X j)) : ℂ) := by
    funext j; rw [neg_mul]
  have e2 : (fun j => (Real.exp (-(-t * X j)) : ℂ)) = fun j => (Real.exp (t * X j) : ℂ) := by
    funext j; rw [neg_mul, neg_neg]
  rw [e1, e2]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h.1, h.2, fromBlocks_one]

theorem tsb_dM_star {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : (dM X t)ᴴ = dM X t := by
  unfold dM
  rw [fromBlocks_conjTranspose, diagonal_conjTranspose, diagonal_conjTranspose, conjTranspose_zero]
  congr 2 <;> (funext j; simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal])

theorem tsb_dM_inG {n : ℕ} (X : Fin n → ℝ) (t : ℝ) : InG (dM X t) := by
  unfold InG
  rw [tsb_dM_star]
  unfold dM JJ
  have h := exp_diagonal_mul_inverse X t
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.one_mul, h.1, h.2, neg_zero]

theorem tsb_dil_exists (n : ℕ) (X : Fin n → ℝ) (t : ℝ) : ∃ a : GR n, IsDil X t a := by
  have h1 := tsb_dM_mul X t
  have h2 : dM X (-t) * dM X t = 1 := by simpa using tsb_dM_mul X (-t)
  exact ⟨⟨⟨dM X t, dM X (-t), h1, h2⟩, tsb_dM_inG X t⟩, rfl⟩

theorem tsb_dil_aZ {n : ℕ} (X : Fin n → ℝ) (t : ℝ) (a : GR n) (h : IsDil X t a) : mR a = aZ X t := by
  rw [h]
  unfold aZ
  congr 2 <;> (funext j; push_cast [Complex.ofReal_exp]; ring_nf)

theorem tsb_aZ_entry {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) :
    (∀ z, aZ X z i j = match i, j with
      | Sum.inl a, Sum.inl b => if a = b then Complex.exp (z * X a) else 0
      | Sum.inr a, Sum.inr b => if a = b then Complex.exp (-(z * X a)) else 0
      | _, _ => 0) := by
  intro z
  rcases i with a | a <;> rcases j with b | b <;> simp [aZ, diagonal_apply]

theorem tsb_aZ_diff {n : ℕ} (X : Fin n → ℝ) (i j : Fin n ⊕ Fin n) : Differentiable ℂ (fun z => aZ X z i j) := by
  have h := tsb_aZ_entry X i j
  simp_rw [h]
  rcases i with a | a <;> rcases j with b | b <;> simp only
  · split_ifs
    · fun_prop
    · exact differentiable_const _
  · exact differentiable_const _
  · exact differentiable_const _
  · split_ifs
    · exact (Complex.differentiable_exp.comp ((differentiable_id.mul (differentiable_const _)).neg))
    · exact differentiable_const _

theorem tsb_aZ_cont {n : ℕ} (X : Fin n → ℝ) : Continuous (fun z => aZ X z) :=
  continuous_pi fun i => continuous_pi fun j => (tsb_aZ_diff X i j).continuous

theorem tsb_det_diffAt {ι : Type} [Fintype ι] [DecidableEq ι] {A : ℂ → Matrix ι ι ℂ} {z : ℂ}
    (h : ∀ i j, DifferentiableAt ℂ (fun w => A w i j) z) : DifferentiableAt ℂ (fun w => (A w).det) z := by
  simp only [Matrix.det_apply]
  refine DifferentiableAt.fun_sum fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  exact (differentiableAt_const _).mul (DifferentiableAt.fun_finset_prod fun i _ => h _ _)

theorem tsb_mul_diff {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n ⊕ Fin n) :
    Differentiable ℂ (fun z => (M * aZ X z) i j) := by
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (tsb_aZ_diff X k j)

theorem differentiable_first_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u1 (M * aZ X z) i j) := by
  simp only [u1, Matrix.add_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.of_apply, smul_eq_mul]
  exact ((differentiable_const _).mul (tsb_mul_diff X M _ _)).add (tsb_mul_diff X M _ _)

theorem differentiable_second_cayley_block_dilation {n : ℕ} (X : Fin n → ℝ) (M : M2 n) (i j : Fin n) :
    Differentiable ℂ (fun z => u2 (M * aZ X z) i j) := by
  simp only [u2, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
    Matrix.of_apply, smul_eq_mul]
  exact (((differentiable_const _).mul (tsb_mul_diff X M _ _)).neg).add (tsb_mul_diff X M _ _)

theorem tsb_det_aZ_ne {n : ℕ} (X : Fin n → ℝ) (z : ℂ) : (aZ X z).det ≠ 0 := by
  unfold aZ
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)
    (Finset.prod_ne_zero_iff.2 fun _ _ => Complex.exp_ne_zero _)

theorem tsbFacts : TSBFacts := by
  intro hD n p q e
  refine ⟨tsb_compact n, tsb_mR_cont n, continuous_spherical_section hD n p q e, tsb_dil_exists n, tsb_dil_aZ, ?_⟩
  intro X C hC
  set Φ : GR n × ℂ → M2 n := fun yz => mR yz.1 * aZ X yz.2 with hΦ
  have hΦc : Continuous Φ := ((tsb_mR_cont n).comp continuous_fst).matrix_mul ((tsb_aZ_cont X).comp continuous_snd)
  set O : Set (GR n × ℂ) := {yz | (u1 (Φ yz)).det ≠ 0 ∧ (u2 (Φ yz)).det ≠ 0} with hO
  have hOo : IsOpen O := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_ne_fun (((continuous_first_cayley_block n).comp hΦc).matrix_det) continuous_const
    · exact isOpen_ne_fun (((continuous_second_cayley_block n).comp hΦc).matrix_det) continuous_const
  have hreal : ∀ (y : GR n) (t : ℝ), (y, (t : ℂ)) ∈ O := by
    intro y t
    obtain ⟨a, ha⟩ := tsb_dil_exists n X t
    have : Φ (y, (t : ℂ)) = mR (y * a) := by
      simp only [hΦ]; rw [← tsb_dil_aZ X t a ha]; rfl
    simp only [hO, Set.mem_setOf_eq, this]
    exact hD n (y * a)
  have tube : ∀ t : ℝ, ∃ v : Set ℂ, IsOpen v ∧ (t : ℂ) ∈ v ∧ C ×ˢ v ⊆ O := by
    intro t
    obtain ⟨u, v, -, hv, hCu, htv, huv⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (t : ℂ))) hOo
      (by rintro ⟨y, z⟩ ⟨-, hz⟩; simp only [Set.mem_singleton_iff] at hz; subst hz; exact hreal y t)
    exact ⟨v, hv, htv rfl, fun yz hyz => huv ⟨hCu hyz.1, hyz.2⟩⟩
  choose v hvo hvt hvC using tube
  refine ⟨⋃ t, v t, isOpen_iUnion hvo, fun t => Set.mem_iUnion.2 ⟨t, hvt t⟩, ?_, ?_⟩
  · intro yz hyz
    obtain ⟨hy, hz⟩ := hyz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : yz ∈ O := hvC t ⟨hy, ht⟩
    have h0 : (Φ yz).det ≠ 0 := by
      simp only [hΦ]; rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    exact ((continuousAt_twisted_section p q e (Φ yz) h0 hmem.1 hmem.2).comp hΦc.continuousAt).continuousWithinAt
  · intro y hy z hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hz
    have hmem : (y, z) ∈ O := hvC t (Set.mk_mem_prod hy ht)
    have h0 : (mR y * aZ X z).det ≠ 0 := by
      rw [det_mul]; exact mul_ne_zero (tsb_det_ne n _) (tsb_det_aZ_ne X _)
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold twistedScalarSection f0
    refine DifferentiableAt.mul ?_ (DifferentiableAt.mul ?_ ?_)
    · exact (tsb_det_diffAt fun i j => (tsb_mul_diff X (mR y) i j).differentiableAt).zpow (Or.inl h0)
    · exact (tsb_det_diffAt fun i j => (differentiable_first_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.1)
    · exact (tsb_det_diffAt fun i j => (differentiable_second_cayley_block_dilation X (mR y) i j).differentiableAt).zpow (Or.inl hmem.2)

end PositivityTheory.Rg.Sw.AbsSt
