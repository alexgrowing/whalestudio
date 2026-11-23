import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatSweepSmoothlyInducedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLMulRightColumnsEqZeroOfRankStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCardStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFiltrationExists

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences Matrix Topology
open scoped TensorProduct

namespace GlobalTheory.RankStrataProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lower

variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype b] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [DecidableEq d] in

theorem _root_.GlobalTheory.RankStrataProof.mul_apply_of_cols {n : Type} (e : c ⊕ d ≃ a) {x : Matrix b a k} (hx : ∀ i j, x i (e (.inr j)) = 0)
    (g : Matrix a n k) (i : b) (l : n) : (x * g) i l = ∑ m, x i (e (.inl m)) * g (e (.inl m)) l := by
  rw [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp [hx]

def rAct (s : Set ℕ) (x : RankIn k a b s) (g : GL a k) : RankIn k a b s :=
  ⟨act x.1 (g, 1), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL a k) : (_root_.GlobalTheory.RankStrataProof.rAct s x g).1 = x.1 * g.val := by
  unfold _root_.GlobalTheory.RankStrataProof.rAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.rAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.rAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL a k) :
    _root_.GlobalTheory.RankStrataProof.rAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.rAct s (_root_.GlobalTheory.RankStrataProof.rAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, _root_.GlobalTheory.RankStrataProof.rAct_val, Units.val_mul, Matrix.mul_assoc]

theorem continuous_rAct (s : Set ℕ) : Continuous fun p : RankIn k a b s × GL a k => rAct s p.1 p.2 := by
  refine Continuous.subtype_mk (f := fun p : RankIn k a b s × GL a k => act p.1.1 (p.2, 1)) ?_ _
  exact (continuous_const.matrix_mul (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (Units.continuous_val.comp continuous_snd)

variable (k b) in

abbrev ColZero (e : c ⊕ d ≃ a) (s : Set ℕ) : Type :=
  {x : RankIn k a b s // ∀ i j, x.1 i (e (.inr j)) = 0}

def pAct (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) : ColZero k b e s :=
  ⟨rAct s y.1 p, fun i j => by
    rw [rAct_val, mul_apply_of_cols e y.2]
    simp [(mem_parabLower_two k).1 p.2]⟩

def fstBlock (e : c ⊕ d ≃ a) : GL c k →* parabLower k (two e) :=
  ((emb₂ k e).codRestrict _ fun _ => leviEmb_mem_parabLower k _ _).comp (MonoidHom.inl _ _)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem pAct_eq (e : c ⊕ d ≃ a) (s : Set ℕ) (y : ColZero k b e s) (p : parabLower k (two e)) :
    pAct e s y (fstBlock e (leviProjLower k (two e) p false)) = pAct e s y p := by
  refine Subtype.ext (Subtype.ext ?_)
  ext i l
  obtain ⟨l | l, rfl⟩ := e.surjective l
  · show (rAct s y.1 _).1 _ _ = (rAct s y.1 _).1 _ _
    rw [rAct_val, rAct_val, mul_apply_of_cols e y.2, mul_apply_of_cols e y.2]
    refine Finset.sum_congr rfl fun m _ => congrArg _ ?_
    exact leviEmb_apply_same k (two e) _ false m l
  · exact ((pAct e s y _).2 i l).trans ((pAct e s y _).2 i l).symm

variable (b) in

def colRep (e : c ⊕ d ≃ a) (s : Set ℕ) (ν : kˣ →* ℂˣ) :
    Representation ℂ (GL c k) (SB (ColZero k b e s)) :=
  twist (sbRep (fun y g => pAct e s y (fstBlock e g))
    (fun y => Subtype.ext (by rw [map_one]; exact rAct_one s y.1))
    (fun y g h => Subtype.ext (by rw [map_mul]; exact rAct_mul s y.1 _ _))
    (fun g => ((continuous_rAct s).comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _))
    (detChar c ν)

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c d : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d] in
theorem _root_.GlobalTheory.RankStrataProof.isSmoothChar_omChar {μ : kˣ →* ℂˣ} (hμ : _root_.GlobalTheory.SmGL.IsSmoothChar μ) : _root_.GlobalTheory.SmGL.IsSmoothChar (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar a b μ) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.omChar
  apply _root_.GlobalTheory.SmGL.IsSmoothChar.mul
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_fst
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul
      (_root_.GlobalTheory.SmGL.IsSmoothChar.inv hμ)
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))
  · refine _root_.GlobalTheory.SmGL.IsSmoothChar.comp ?_ _ continuous_snd
    apply _root_.GlobalTheory.SmGL.IsSmoothChar.detChar
    exact _root_.GlobalTheory.SmGL.IsSmoothChar.mul hμ
      (_root_.GlobalTheory.SmGL.isSmoothChar_of_isUnram (_root_.GlobalTheory.SmGL.isUnram_absPow k _))

theorem lower (e : c ⊕ d ≃ a) {κ : ℕ} (hκ : κ = Fintype.card c) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (z : ℂ) (hz : z + (Fintype.card c : ℂ) / 2 = (Fintype.card b : ℂ) / 2) :
    Nonempty (Representation.Equiv ((omegaOn a b μ {κ}).comp (MonoidHom.inl _ _))
      (ind₂Lower e (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))))) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hcl : IsClosed {x : RankIn k a b {κ} | ∀ i j, x.1 i (e (.inr j)) = 0} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_subtype_val.matrix_elem _ _) continuous_const
  obtain ⟨E, hE⟩ := GlobalTheory.T.schwartzBruhat_sweep_smoothly_induced (GL a k) (RankIn k a b {κ}) (ColZero k b e {κ})
    (SB (ColZero k b e {κ}) ⊗[ℂ] ℂ) (rAct {κ}) (rAct_one _) (rAct_mul _) (continuous_rAct _)
    Subtype.val hcl.isClosedEmbedding_subtypeVal (parabLower k (two e)) (KO k a) SplitFlip.isCompact_KO
    (fun x => by
      obtain ⟨g, hg⟩ := GlobalTheory.T.exists_GL_mul_rightColumns_eq_zero_of_rank k b c d a e x.1 (x.2.trans hκ)
      obtain ⟨p, hp, w, hw, h⟩ := iwasawa_blockTriangular k a (fun i => (!blk (two e) i).toNat) g⁻¹
      have hp' : p ∈ parabLower k (two e) := (mem_parabLower_two k).2 fun i j => hp (by
        rw [← two_false e, ← two_true e]; simp only [blk_apply]; simp)
      refine ⟨pAct e _ ⟨rAct _ x g, by rwa [rAct_val]⟩ ⟨p, hp'⟩, w, hw, ?_⟩
      show x = rAct _ (rAct _ (rAct _ x g) p) w
      rw [← rAct_mul, ← rAct_mul, ← h, mul_inv_cancel, rAct_one])
    (pAct e _) (fun _ _ => rfl)
    (fun y y' g h => (mem_parabLower_two k).2 fun i j => by
      refine congrFun (GlobalTheory.T.leftColumns_mulVec_injective_of_rank_eq_card k b c d a e y.1.1 (y.1.2.trans hκ) y.2
        (fun m => g.val (e (.inl m)) (e (.inr j))) (funext fun l => ?_)) i
      have := y'.2 l j
      rw [← h, rAct_val, mul_apply_of_cols e y.2] at this
      exact this)
    ((omChar a b μ).comp (MonoidHom.inl _ _))
    ((isSmoothChar_omChar hμ).comp _ (continuous_id.prodMk continuous_const))
    ((twist (MonoidHom.comp (extTensor (colRep b e {κ}
        (μ⁻¹ * absPow k ((Fintype.card b : ℂ) / 2 + (Fintype.card d : ℂ) / 2)))
        (detRep d (μ⁻¹ * absPow k z))) (leviTwo k c d).symm.toMonoidHom) (deltaHalf k (Two c d))⁻¹).comp
        (leviProjLower k (two e)))
    (TensorProduct.rid ℂ _)
    (fun p w y => by
      obtain ⟨φ, rfl⟩ := (TensorProduct.rid ℂ _).symm.surjective w
      set m := leviProjLower k (two e) p with hm
      have hd : GeneralLinearGroup.det (p : GL a k) =
          GeneralLinearGroup.det (m false) * GeneralLinearGroup.det (m true) := by
        have := det_parab k (opp (two e)) p
        rw [this]
        exact (Fintype.prod_bool _).trans (mul_comm _ _)
      have hδ := deltaHalf_two (k := k) (m false, m true)
      rw [show leviTwo k c d (m false, m true) = m from (leviTwo k c d).right_inv m] at hδ
      rw [LinearEquiv.apply_symm_apply, TensorProduct.rid_symm_apply]
      show (TensorProduct.rid ℂ _ ((((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) •
        extTensor _ _ (m false, m true) (φ ⊗ₜ 1))).1 y = _
      rw [extTensor_tmul, map_smul, TensorProduct.rid_tmul]
      show (((deltaHalf k (Two c d) m)⁻¹ : ℂˣ) : ℂ) * (detRep d _ (m true) 1 *
        ((detChar c _ (m false) : ℂ) * φ.1 (pAct e _ y (fstBlock e (m false))))) = _
      rw [pAct_eq, ← mul_assoc, ← mul_assoc, detRep, ofChar_apply, mul_one, ← Units.val_mul, ← Units.val_mul]
      congr 2
      rw [hδ]
      simp only [omChar, MonoidHom.comp_apply, MonoidHom.mul_apply, detChar_apply, MonoidHom.inl_apply,
        MonoidHom.coe_fst, MonoidHom.coe_snd, map_one, mul_one, hd, map_mul, neg_div, absPow_neg,
        MonoidHom.inv_apply]
      have h1 := DFunLike.congr_fun (absPow_add k z ((Fintype.card c : ℂ) / 2))
        (GeneralLinearGroup.det (m true))
      rw [hz] at h1
      rw [h1, absPow_add]
      simp only [MonoidHom.mul_apply, mul_inv, inv_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp)
  refine ⟨.mk E fun g => LinearMap.ext fun Φ => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
  refine (TensorProduct.rid ℂ _).injective (Subtype.ext (funext fun y => ?_))
  refine (hE _ x y).trans (Eq.trans ?_ (hE Φ (x * g) y).symm)
  rw [map_mul, rAct_mul, Units.val_mul, mul_assoc]
  rfl

end Lower

section Open

variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]

theorem isLocallyConstant_char {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : IsLocallyConstant fun y => (ψ y : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set G)) := IsOpen.preimage (by fun_prop) h
  filter_upwards [this.mem_nhds (show x ∈ _ by simp)] with y hy
  have hy' : ψ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at hy'
  rw [hy']

def divChar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* ℂˣ} (h : IsSmoothChar ψ) : SB G ≃ₗ[ℂ] SB G where
  toFun w := ⟨fun y => (ψ⁻¹ y : ℂ) * w.1 y, (isLocallyConstant_char h.inv).mul w.2.1, w.2.2.mul_left⟩
  invFun w := ⟨fun y => (ψ y : ℂ) * w.1 y, (isLocallyConstant_char h).mul w.2.1, w.2.2.mul_left⟩
  map_add' _ _ := Subtype.ext (funext fun _ => mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => mul_left_comm _ _ _)
  left_inv w := Subtype.ext (funext fun y => by simp)
  right_inv w := Subtype.ext (funext fun y => by simp)

def topM (e : a ⊕ c ≃ b) (y : Matrix a a k) : Matrix b a k := (fromRows y 0).submatrix e.symm id

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inl (e : a ⊕ c ≃ b) (y : Matrix a a k) (i l : a) : topM e y (e (.inl i)) l = y i l := by
  simp [topM]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype c] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype a] [Fintype b] in
@[simp] theorem topM_inr (e : a ⊕ c ≃ b) (y : Matrix a a k) (i : c) (l : a) :
    topM e y (e (.inr i)) l = 0 := by
  simp [topM]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] in
theorem mul_topM (e : a ⊕ c ≃ b) (g : Matrix b b k) (y : Matrix a a k) (i : b) (l : a) :
    (g * topM e y) i l = ∑ m, g i (e (.inl m)) * y m l := by
  rw [mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
  simp

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq a]
  [DecidableEq b] [DecidableEq c] [Fintype c] [Fintype b] in
theorem topM_mul (e : a ⊕ c ≃ b) (y g : Matrix a a k) : topM e (y * g) = topM e y * g := by
  ext i l
  obtain ⟨i | i, rfl⟩ := e.surjective i <;> simp [mul_apply]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq b] [DecidableEq c] in
theorem rank_topM (e : a ⊕ c ≃ b) (y : GL a k) : (topM e y.val).rank = Fintype.card a := by
  refine le_antisymm (rank_le_card_width _) ?_
  have h : (topM e y.val).submatrix (fun i => e (.inl i)) (Equiv.refl a) = y.val := by
    ext i l; simp
  have h2 := rank_submatrix_le (topM e y.val) (fun i => e (.inl i)) (Equiv.refl a)
  rwa [h, rank_of_isUnit _ y.isUnit] at h2

def topEmb (e : a ⊕ c ≃ b) {κ : ℕ} (hκ : κ = Fintype.card a) (y : GL a k) : RankIn k a b {κ} :=
  ⟨topM e y.val, (rank_topM e y).trans hκ.symm⟩

def lAct (s : Set ℕ) (x : RankIn k a b s) (h : GL b k) : RankIn k a b s :=
  ⟨act x.1 (1, h), by rw [rank_act]; exact x.2⟩

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_val (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g : GL b k) : (_root_.GlobalTheory.RankStrataProof.lAct s x g).1 = (g⁻¹).val * x.1 := by
  unfold _root_.GlobalTheory.RankStrataProof.lAct _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.act
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_one (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) : _root_.GlobalTheory.RankStrataProof.lAct s x 1 = x := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val]
  simp

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.RankStrataProof.lAct_mul (s : Set ℕ) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s) (g h : GL b k) :
    _root_.GlobalTheory.RankStrataProof.lAct s x (g * h) = _root_.GlobalTheory.RankStrataProof.lAct s (_root_.GlobalTheory.RankStrataProof.lAct s x g) h := by
  apply Subtype.ext
  rw [_root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.GlobalTheory.RankStrataProof.lAct_val, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

open Matrix Topology Module in
open scoped TensorProduct in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c] in
theorem _root_.GlobalTheory.RankStrataProof.continuous_lAct (s : Set ℕ) : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => _root_.GlobalTheory.RankStrataProof.lAct s p.1 p.2 := by
  have h : Continuous fun p : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a b s × GL b k => ((p.2⁻¹ : GL b k) : Matrix b b k) * p.1.1 :=
    (Units.continuous_val.comp (continuous_inv.comp continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst)
  refine Continuous.subtype_mk (h.congr fun p => (_root_.GlobalTheory.RankStrataProof.lAct_val s p.1 p.2).symm) _

end Open

end GlobalTheory.RankStrataProof
