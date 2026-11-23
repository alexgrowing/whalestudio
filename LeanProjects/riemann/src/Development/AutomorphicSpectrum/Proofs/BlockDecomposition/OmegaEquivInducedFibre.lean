import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

def topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inl (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : c) (l : a) :
    topR e y (e (.inl i)) l = y i l := by
  simp [topR]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] in
@[simp] theorem topR_inr (e : c ⊕ d ≃ b) (y : Matrix c a k) (i : d) (l : a) :
    topR e y (e (.inr i)) l = 0 := by
  simp [topR]

theorem mul_topR (e : c ⊕ d ≃ b) (g : Matrix b b k) (y : Matrix c a k) (i : b) (l : a) :
    (g * topR e y) i l = ∑ m, g i (e (.inl m)) * y m l := by
  rw [mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp

theorem topR_mul (e : c ⊕ d ≃ b) (y : Matrix c a k) (g : Matrix a a k) :
    topR e (y * g) = topR e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [mul_apply]

theorem rank_topR (e : c ⊕ d ≃ b) (y : Matrix c a k) : (topR e y).rank = y.rank := by
  refine le_antisymm ?_ ?_
  · have h : topR e y = ((1 : Matrix b b k).submatrix id fun i => e (.inl i)) * y := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp [mul_apply, one_apply]
      · simp [mul_apply, one_apply]
    rw [h]
    exact rank_mul_le_right _ _
  · have h : (topR e y).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y := by
      ext i l; simp
    have h2 := rank_submatrix_le (topR e y) (fun i => e (.inl i)) (Equiv.refl a)
    rwa [h] at h2

def topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) : RankIn k a b {κ} :=
  ⟨topR e y.1, (rank_topR e y.1).trans y.2⟩

theorem range_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    Set.range (topEmbR (k := k) (a := a) e (κ := κ)) = {x | ∀ j i, x.1 (e (.inr j)) i = 0} := by
  ext x
  refine ⟨?_, fun hx => ?_⟩
  · rintro ⟨y, rfl⟩ j i
    exact topR_inr e _ j i
  · have hxy : x.1 = topR e (x.1.submatrix (fun i => e (.inl i)) id) := by
      ext i l
      obtain ⟨i | i, rfl⟩ := e.surjective i
      · simp
      · simpa using hx i l
    have hr : (x.1.submatrix (fun i => e (.inl i)) id).rank = κ := by
      rw [← rank_topR e, ← hxy]
      exact x.2
    exact ⟨⟨_, hr⟩, Subtype.ext hxy.symm⟩

theorem isClosedEmbedding_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} :
    IsClosedEmbedding (topEmbR (k := k) (a := a) e (κ := κ)) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨IsEmbedding.of_comp (g := fun x : RankIn k a b {κ} => x.1.submatrix (fun i => e (.inl i)) id)
    (Continuous.subtype_mk (continuous_matrix fun i l => ?_) _)
    (continuous_subtype_val.matrix_submatrix _ _) ?_, ?_⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective i
    · simp only [topR_inl]
      exact continuous_subtype_val.matrix_elem _ _
    · simp only [topR_inr]
      exact continuous_const
  · convert IsEmbedding.subtypeVal (p := fun y : Matrix c a k => y.rank ∈ ({κ} : Set ℕ)) using 1
    funext y
    ext i l
    exact topR_inl e _ i l
  · rw [range_topEmbR]
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const

theorem lAct_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (y : RankIn k a c {κ}) (p : parab k (two e)) :
    lAct _ (topEmbR e y) p = topEmbR e (lAct _ y (show GL c k from leviProj k (two e) p false)) := by
  refine Subtype.ext ?_
  rw [lAct_val]
  ext i l
  refine (mul_topR e _ _ i l).trans ?_
  obtain ⟨i | i, rfl⟩ := e.surjective i
  · refine Eq.trans ?_ (topR_inl e _ i l).symm
    rw [lAct_val]
    have : (show GL c k from leviProj k (two e) p false)⁻¹ = leviProj k (two e) p⁻¹ false := by
      rw [map_inv]; rfl
    rw [this]
    rfl
  · refine Eq.trans ?_ (topR_inr e _ i l).symm
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [(mem_parab_two k).1 (inv_mem p.2), zero_mul]

theorem eq_zero_of_vecMul (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (y : RankIn k a c {κ})
    (v : c → k) (h : v ᵥ* y.1 = 0) : v = 0 := by
  refine GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k a c d b e (topR e y.1)ᵀ
    ((rank_transpose _).trans (((rank_topR e y.1).trans y.2).trans hκ)) (fun i j => topR_inr e _ j i) v ?_
  have hs : (topR e y.1)ᵀ.submatrix id (fun i => e (.inl i)) = y.1ᵀ := by
    ext i l; simp
  rw [hs, mulVec_transpose, h]

theorem exists_topEmbR (e : c ⊕ d ≃ b) {κ : ℕ} (hκ : κ = Fintype.card c) (x : RankIn k a b {κ}) :
    ∃ y, ∃ w ∈ KO k b, x = lAct _ (topEmbR e y) w := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k a c d b e x.1ᵀ ((rank_transpose _).trans (x.2.trans hκ))
  obtain ⟨u, hu⟩ := (isUnit_transpose _).2 g.isUnit
  obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k b (fun i => (blk (two e) i).toNat) u
  have hp' : p ∈ parab k (two e) := (mem_parab_two k).2 fun i j => hp (by
    rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
  have : lAct _ x u⁻¹ ∈ Set.range (topEmbR (k := k) (a := a) e (κ := κ)) := by
    rw [range_topEmbR]
    intro j i
    rw [lAct_val, inv_inv, hu, ← transpose_transpose x.1, ← transpose_mul]
    exact hg i j
  obtain ⟨y, hy⟩ := this
  refine ⟨_, w, hw, Eq.trans ?_ (congrArg (lAct _ · w) (lAct_topEmbR e y ⟨p, hp'⟩))⟩
  show x = lAct _ (lAct _ _ p) w
  rw [hy, ← lAct_mul, ← lAct_mul, ← h, inv_mul_cancel, lAct_one]

theorem fibChar_fst (e : c ⊕ d ≃ b) (μ : kˣ →* ℂˣ) (γ : GL a k) :
    fibChar a c d μ (γ, 1, 1) = omChar a b μ (γ, 1) := by
  have hb : ((Fintype.card c : ℂ) + Fintype.card d) / 2 = (Fintype.card b : ℂ) / 2 := by
    rw [← Fintype.card_congr e, Fintype.card_sum]; push_cast; ring
  simp [fibChar, omChar, hb]

theorem fibStr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a b c d : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d] (e : c ⊕ d ≃ b) (κ : ℕ), κ = Fintype.card c → ∀ μ : kˣ →* ℂˣ,
    IsSmoothChar μ → Nonempty ((omegaOn a b μ {κ}).Equiv (indSnd e (fibRep a c d μ κ))) := by
  intro k _ _ _ _ a b c d _ _ _ _ _ _ _ _ e κ hκ μ hμ
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL b k) (RankIn k a b {κ}) (RankIn k a c {κ})
    (SB (RankIn k a c {κ})) (lAct {κ}) (lAct_one _) (lAct_mul _) (continuous_lAct _)
    (topEmbR e) (isClosedEmbedding_topEmbR e) (parab k (two e)) (KO k b) SplitFlip.isCompact_KO
    (exists_topEmbR e hκ)
    (fun y p => lAct _ y (show GL c k from leviProj k (two e) p false)) (lAct_topEmbR e)
    (fun y y' g h => by
      refine inv_mem_iff.1 ((mem_parab_two k).2 fun j i => ?_)
      have h0 : (fun m => (g⁻¹).val (e (.inr j)) (e (.inl m))) ᵥ* y.1 = 0 := by
        funext l
        have := congrArg (fun x : RankIn k a b {κ} => x.1 (e (.inr j)) l) h
        simp only [lAct_val] at this
        exact (mul_topR e _ _ _ l).symm.trans (this.trans (topR_inr e _ j l))
      exact congrFun (eq_zero_of_vecMul e hκ y _ h0) i)
    ((omChar a b μ).comp (MonoidHom.inr _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_const.prodMk continuous_id))
    ((twist (MonoidHom.comp ((fibRep a c d μ κ).comp (MonoidHom.inr _ _)) (leviTwo k c d).symm.toMonoidHom)
      (deltaHalf k (Two c d))).comp (leviProj k (two e)))
    (LinearEquiv.refl ℂ _)
    (fun p w y => by
      set m := leviProj k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL b k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) :=
        (det_parab k (two e) p).trans ((Fintype.prod_bool _).trans (mul_comm _ _))
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      show (deltaHalf k (Two c d) m : ℂ) * (fibRep a c d μ κ (1, m false, m true) w).1 y = _
      rw [fibRep_apply, ← mul_assoc, ← Units.val_mul]
      refine congrArg₂ _ (congrArg _ ?_) rfl
      rw [hδ]
      simp only [fibChar, omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply,
        MonoidHom.inr_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, one_mul, hd, map_mul,
        neg_div, absPow_neg, MonoidHom.inv_apply, absPow_add, mul_inv, inv_inv, inv_one]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  have hE' : ∀ Φ g y, ((E Φ).1.1 g).1 y =
      (omChar a b μ (1, g) : ℂ) * Φ.1 (lAct _ (topEmbR e y) g) := hE
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x =>
    Subtype.ext (funext fun y => ?_)))⟩
  obtain ⟨γ, h⟩ := g
  refine (hE' _ x y).trans (Eq.trans ?_ (fibRep_apply a c d μ κ γ 1 1 ((E Φ).1.1 (x * h)) y).symm)
  rw [hE', omegaOn_apply, fibChar_fst e, ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul,
    ← map_mul, ← map_mul]
  refine congrArg₂ _ (congrArg _ (congrArg _ (by simp))) (congrArg _ (Subtype.ext ?_))
  simp only [lAct_val, act, topEmbR, Units.val_mul, topR_mul, _root_.mul_inv_rev, Matrix.mul_assoc,
    Units.val_one, Matrix.one_mul, inv_one, Matrix.mul_one]

end GlobalTheory.CompanionTheory.ThetaGLLen
