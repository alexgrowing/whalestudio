import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.SESymmApply
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.GramBlockUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.NatSmulMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBBounded
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.DiagMulOfBt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.AtNormRep
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

noncomputable section

open scoped Classical
open NumberField Matrix

namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes

section Tri

variable {K : Type*} [Field K] {n : ℕ}

theorem loUni_block {L : Matrix (Fin n) (Fin n) K} (h : Formalism.MainNotions.S.IsLoUni L) : L.BlockTriangular OrderDual.toDual :=
  fun i j hij => (h i j).1 hij

theorem det_loUni {L : Matrix (Fin n) (Fin n) K} (h : Formalism.MainNotions.S.IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular L (loUni_block h)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

theorem loUni_inv {L : Matrix (Fin n) (Fin n) K} (h : Formalism.MainNotions.S.IsLoUni L) : Formalism.MainNotions.S.IsLoUni L⁻¹ := by
  have hu : IsUnit L.det := by rw [det_loUni h]; exact isUnit_one
  haveI := Matrix.invertibleOfIsUnitDet L hu
  have hb := Matrix.blockTriangular_inv_of_blockTriangular (loUni_block h)
  intro i j
  refine ⟨fun hij => hb hij, fun hij => ?_⟩
  subst hij
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv L hu) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  rw [Finset.sum_eq_single i] at h1
  · rwa [(h i i).2 rfl, one_mul] at h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hb (show OrderDual.toDual i < OrderDual.toDual k from hk), mul_zero]
    · rw [(h i k).1 hk, zero_mul]
  · simp

theorem up_conjT {E : Type} [Field E] [StarRing E] {M : Matrix (Fin n) (Fin n) E}
    (h : Formalism.MainNotions.S.IsLoUni M) : Formalism.MainNotions.S.IsUpUni M.conjTranspose := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩

theorem strictLo_last {r : ℕ} {M : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Formalism.MainNotions.S.IsLoUni M) :
    (M - 1) *ᵥ Pi.single (Fin.last r) 1 = 0 := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Pi.zero_apply, Matrix.sub_apply]
  by_cases hi : i = Fin.last r
  · subst hi; rw [(h _ _).2 rfl, Matrix.one_apply_eq, sub_self]
  · have hlt : i < Fin.last r := lt_of_le_of_ne (Fin.le_last i) hi
    rw [(h _ _).1 hlt, Matrix.one_apply_ne hi, sub_self]

end Tri

section Twist

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}
  (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T')

def gg : Fin (r + 1) ⊕ Fin (r + 1) → S.V := Sum.elim F.fvec F'.fvec

def Jc (c : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem hT_fvec {T0 : E} (F0 : Formalism.MainNotions.S.FlagG S r T0) (i j : Fin (r + 1)) :
    S.hT (F0.fvec i) (F0.fvec j) = Jc (-T0) i j := by
  unfold Jc
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [Formalism.MainNotions.S.FlagG.fvec, F0.z_norm]
  · have h := F0.z_orth b
    simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last b).ne h'.2), ← S.herm.eq, h, map_zero]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last a).ne h'.1), F0.z_orth a]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    rw [if_neg (fun h' => (Fin.castSucc_lt_last a).ne h'.1), F0.e_iso a b]

theorem gram_gg : gramOf (gg F F') =
    Matrix.fromBlocks (Jc (-T)) (Formalism.MainNotions.S.Zhat F F') (Formalism.MainNotions.S.Zhat F F').conjTranspose (Jc (-T')) := by
  ext (a | a) (b | b)
  · simp [gramOf, gg, hT_fvec]
  · simp [gramOf, gg, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
  · simp only [gramOf, gg, Sum.elim_inr, Sum.elim_inl, Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply,
      Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS]
    rw [← S.herm.eq]; rfl
  · simp [gramOf, gg, hT_fvec]

theorem gram_gg_unit (hTs : star T = T) (hT's : star T' = T') (hZ : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (hG : Formalism.MainNotions.S.Gflag F F' ≠ 0) : IsUnit (gramOf (gg F F')).det := by
  rw [gram_gg]
  refine gram_block_unit (Formalism.MainNotions.S.Zhat F F') T T' hTs hT's hZ hG _ (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_) (fun a b => ?_)
  · simp [Jc]
  · simp
  · simp [Matrix.conjTranspose_apply]
  · simp [Jc]

theorem Jc_conj {c : E} {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) :
    P.conjTranspose * Jc c * P = Jc c := by
  have hlast : ∀ j, P (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
    intro j
    by_cases hj : j = Fin.last r
    · subst hj; rw [if_pos rfl, (hP _ _).2 rfl]
    · rw [if_neg hj, (hP _ _).1 (lt_of_le_of_ne (Fin.le_last j) hj)]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Jc]
  simp only [mul_ite, mul_zero, ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp only [if_true, hlast]
    by_cases hi : i = Fin.last r <;> by_cases hj : j = Fin.last r <;> simp [hi, hj]
  · intro k _ hk; simp [hk]
  · simp

def UU (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  Matrix.fromBlocks P 0 0 P'

theorem UU_isom {P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) (hP' : Formalism.MainNotions.S.IsUpUni P')
    (hZ : P.conjTranspose * Formalism.MainNotions.S.Zhat F F' * P' = Formalism.MainNotions.S.Zhat F F') :
    (UU P P').conjTranspose * gramOf (gg F F') * UU P P' = gramOf (gg F F') := by
  have hZ' : P'.conjTranspose * (Formalism.MainNotions.S.Zhat F F').conjTranspose * P = (Formalism.MainNotions.S.Zhat F F').conjTranspose := by
    have := congrArg Matrix.conjTranspose hZ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
    rw [Matrix.mul_assoc]; exact this
  rw [gram_gg, UU, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [Jc_conj hP, Jc_conj hP', hZ, hZ']

theorem UU_mul (P P' Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : UU P P' * UU Q Q' = UU (P * Q) (P' * Q') := by
  simp [UU, Matrix.fromBlocks_multiply]

theorem UU_one : UU (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) 1 = 1 := by
  simp [UU, Matrix.fromBlocks_one]

end Twist

section Act

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}
  (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T')

theorem UU_sub_one (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    UU P P' - 1 = Matrix.fromBlocks (P - 1) 0 0 (P' - 1) := by
  rw [← UU_one]
  ext (i | i) (j | j) <;> simp [UU, Matrix.one_apply]

theorem UU_mulVec_inl (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c : Fin (r + 1) ⊕ Fin (r + 1) → E)
    (b : Fin (r + 1)) :
    ((UU P P' - 1) *ᵥ c) (Sum.inl b) = ((P - 1) *ᵥ fun k => c (Sum.inl k)) b := by
  rw [UU_sub_one]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem UU_mulVec_inr (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c : Fin (r + 1) ⊕ Fin (r + 1) → E)
    (b : Fin (r + 1)) :
    ((UU P P' - 1) *ᵥ c) (Sum.inr b) = ((P' - 1) *ᵥ fun k => c (Sum.inr k)) b := by
  rw [UU_sub_one]
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem sL_sub (X : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E) (x : S.V) :
    sL (gg F F') X x - x = (∑ b, ((X - 1) *ᵥ cOf (gg F F') x) (Sum.inl b) • F.fvec b) +
      ∑ b, ((X - 1) *ᵥ cOf (gg F F') x) (Sum.inr b) • F'.fvec b := by
  rw [sL_apply, add_sub_cancel_left, Fintype.sum_sum_type]
  rfl

theorem sL_frame (hG : IsUnit (gramOf (gg F F')).det) (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (b : Fin (r + 1)) : sL (gg F F') (UU P P') (F.fvec b) = ∑ c, P c b • F.fvec c := by
  have h := sL_sub F F' (UU P P') (F.fvec b)
  have hc : cOf (gg F F') (F.fvec b) = Pi.single (Sum.inl b) 1 := cOf_g (gg F F') hG (Sum.inl b)
  simp only [UU_mulVec_inl, UU_mulVec_inr, hc] at h
  have e1 : (fun k : Fin (r + 1) => (Pi.single (Sum.inl b) (1 : E) : Fin (r + 1) ⊕ Fin (r + 1) → E) (Sum.inl k)) =
      Pi.single b 1 := by
    ext k; by_cases hk : k = b <;> simp [Pi.single_apply, hk]
  have e2 : (fun k : Fin (r + 1) => (Pi.single (Sum.inl b) (1 : E) : Fin (r + 1) ⊕ Fin (r + 1) → E) (Sum.inr k)) = 0 := by
    ext k; simp [Pi.single_apply]
  rw [e1, e2, Matrix.mulVec_zero] at h
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h
  have hcol : ∀ x, ((P - 1) *ᵥ Pi.single b (1 : E)) x = P x b - (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) x b := by
    intro x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← sub_add_cancel (sL (gg F F') (UU P P') (F.fvec b)) (F.fvec b), h,
    Finset.sum_congr rfl (fun x _ => by rw [hcol x])]
  simp only [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

theorem sL_frame' (hG : IsUnit (gramOf (gg F F')).det) (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (b : Fin (r + 1)) : sL (gg F F') (UU P P') (F'.fvec b) = ∑ c, P' c b • F'.fvec c := by
  have h := sL_sub F F' (UU P P') (F'.fvec b)
  have hc : cOf (gg F F') (F'.fvec b) = Pi.single (Sum.inr b) 1 := cOf_g (gg F F') hG (Sum.inr b)
  simp only [UU_mulVec_inl, UU_mulVec_inr, hc] at h
  have e1 : (fun k : Fin (r + 1) => (Pi.single (Sum.inr b) (1 : E) : Fin (r + 1) ⊕ Fin (r + 1) → E) (Sum.inr k)) =
      Pi.single b 1 := by
    ext k; by_cases hk : k = b <;> simp [Pi.single_apply, hk]
  have e2 : (fun k : Fin (r + 1) => (Pi.single (Sum.inr b) (1 : E) : Fin (r + 1) ⊕ Fin (r + 1) → E) (Sum.inl k)) = 0 := by
    ext k; simp [Pi.single_apply]
  rw [e1, e2, Matrix.mulVec_zero] at h
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at h
  have hcol : ∀ x, ((P' - 1) *ᵥ Pi.single b (1 : E)) x = P' x b - (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) x b := by
    intro x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← sub_add_cancel (sL (gg F F') (UU P P') (F'.fvec b)) (F'.fvec b), h,
    Finset.sum_congr rfl (fun x _ => by rw [hcol x])]
  simp only [sub_smul, Finset.sum_sub_distrib, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

end Act

section Orth

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T T' : E}
  (F : Formalism.MainNotions.S.FlagG S r T) (F' : Formalism.MainNotions.S.FlagG S r T')

theorem Jc_mulVec_ne {c0 : E} (v : Fin (r + 1) → E) {a : Fin (r + 1)} (ha : a ≠ Fin.last r) :
    (Jc c0 *ᵥ v) a = 0 := by
  simp [Jc, Matrix.mulVec, dotProduct, ha]

theorem upUni_last {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) (v : Fin (r + 1) → E) :
    ((P - 1) *ᵥ v) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = Fin.last r
  · subst hk; rw [(hP _ _).2 rfl, Matrix.one_apply_eq, sub_self, zero_mul]
  · have hlt : k < Fin.last r := lt_of_le_of_ne (Fin.le_last k) hk
    rw [(hP _ _).1 hlt, Matrix.one_apply_ne (Ne.symm hk), sub_self, zero_mul]

theorem conj_sub_one {Z Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZ : IsUnit Z.det) :
    Z⁻¹ * Q * Z - 1 = Z⁻¹ * (Q - 1) * Z := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.nonsing_inv_mul Z hZ]

theorem kill_single {Z Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hQ : Formalism.MainNotions.S.IsLoUni Q)
    {v : Fin (r + 1) → E} (hv : Z *ᵥ v = Pi.single (Fin.last r) ((Z *ᵥ v) (Fin.last r))) :
    (Z⁻¹ * (Q - 1) * Z) *ᵥ v = 0 := by
  rw [← Matrix.mulVec_mulVec, hv, ← Matrix.mulVec_mulVec]
  have : (Pi.single (Fin.last r) ((Z *ᵥ v) (Fin.last r)) : Fin (r + 1) → E) =
      ((Z *ᵥ v) (Fin.last r)) • Pi.single (Fin.last r) 1 := by
    ext k; by_cases hk : k = Fin.last r <;> simp [Pi.single_apply, hk]
  rw [this, Matrix.mulVec_smul, strictLo_last hQ, smul_zero, Matrix.mulVec_zero]

theorem sum_last_span {P : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hP : Formalism.MainNotions.S.IsUpUni P) {T0 : E}
    (F0 : Formalism.MainNotions.S.FlagG S r T0) (v : Fin (r + 1) → E) :
    (∑ b, ((P - 1) *ᵥ v) b • F0.fvec b) ∈ Submodule.span E (Set.range F0.e) := by
  rw [Fin.sum_univ_castSucc, upUni_last hP, zero_smul, add_zero]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem sL_orth (hG : IsUnit (gramOf (gg F F')).det) {P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hPu : Formalism.MainNotions.S.IsUpUni P) (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').det)
    (hrel : P' = (Formalism.MainNotions.S.Zhat F F')⁻¹ * (P.conjTranspose)⁻¹ * Formalism.MainNotions.S.Zhat F F')
    (hPl : Formalism.MainNotions.S.IsLoUni (P.conjTranspose)⁻¹) (x : S.V) (hx : ∀ a : Fin r, S.hT (F.e a) x = 0) :
    sL (gg F F') (UU P P') x - x ∈ Submodule.span E (Set.range F.e) := by
  rw [sL_sub]
  simp only [UU_mulVec_inl, UU_mulVec_inr]
  set c := cOf (gg F F') x
  have hg := gram_cOf (gg F F') hG x
  rw [gram_gg, Matrix.fromBlocks_mulVec] at hg
  have hrow : ∀ a, (Jc (-T) *ᵥ fun k => c (Sum.inl k)) a + (Formalism.MainNotions.S.Zhat F F' *ᵥ fun k => c (Sum.inr k)) a =
      S.hT (F.fvec a) x := fun a => congrFun hg (Sum.inl a)
  have hZc : Formalism.MainNotions.S.Zhat F F' *ᵥ (fun k => c (Sum.inr k)) =
      Pi.single (Fin.last r) ((Formalism.MainNotions.S.Zhat F F' *ᵥ fun k => c (Sum.inr k)) (Fin.last r)) := by
    ext a
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · rw [Pi.single_apply, if_neg ha]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 ha
      have h1 := hrow (Fin.castSucc i)
      rw [Jc_mulVec_ne _ ha, zero_add] at h1
      rw [h1]
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact hx i
  have h0 : (P' - 1) *ᵥ (fun k => c (Sum.inr k)) = 0 := by
    rw [hrel, conj_sub_one hZu]
    exact kill_single hPl hZc
  rw [h0]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  exact sum_last_span hPu F _

theorem sL_orth' (hG : IsUnit (gramOf (gg F F')).det) {P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hP'u : Formalism.MainNotions.S.IsUpUni P') (hZu : IsUnit (Formalism.MainNotions.S.Zhat F F').conjTranspose.det)
    (hrel : P = ((Formalism.MainNotions.S.Zhat F F').conjTranspose)⁻¹ * (P'.conjTranspose)⁻¹ * (Formalism.MainNotions.S.Zhat F F').conjTranspose)
    (hPl : Formalism.MainNotions.S.IsLoUni (P'.conjTranspose)⁻¹) (x : S.V) (hx : ∀ a : Fin r, S.hT (F'.e a) x = 0) :
    sL (gg F F') (UU P P') x - x ∈ Submodule.span E (Set.range F'.e) := by
  rw [sL_sub]
  simp only [UU_mulVec_inl, UU_mulVec_inr]
  set c := cOf (gg F F') x
  have hg := gram_cOf (gg F F') hG x
  rw [gram_gg, Matrix.fromBlocks_mulVec] at hg
  have hrow : ∀ a, ((Formalism.MainNotions.S.Zhat F F').conjTranspose *ᵥ fun k => c (Sum.inl k)) a +
      (Jc (-T') *ᵥ fun k => c (Sum.inr k)) a = S.hT (F'.fvec a) x := fun a => congrFun hg (Sum.inr a)
  have hZc : (Formalism.MainNotions.S.Zhat F F').conjTranspose *ᵥ (fun k => c (Sum.inl k)) =
      Pi.single (Fin.last r) (((Formalism.MainNotions.S.Zhat F F').conjTranspose *ᵥ fun k => c (Sum.inl k)) (Fin.last r)) := by
    ext a
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · rw [Pi.single_apply, if_neg ha]
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 ha
      have h1 := hrow (Fin.castSucc i)
      rw [Jc_mulVec_ne _ ha, add_zero] at h1
      rw [h1]
      simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact hx i
  have h0 : (P - 1) *ᵥ (fun k => c (Sum.inl k)) = 0 := by
    rw [hrel, conj_sub_one hZu]
    exact kill_single hPl hZc
  rw [h0]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
  exact sum_last_span hP'u F' _

theorem sL_Xa (hG : IsUnit (gramOf (gg F F')).det) {P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hPu : Formalism.MainNotions.S.IsUpUni P) (j : ℕ) (x : S.V) (hx : x ∈ F.Xa (j + 1)) :
    sL (gg F F') (UU P P') x - x ∈ F.Xa j := by
  have hle : F.Xa (j + 1) ≤ (F.Xa j).comap (sL (gg F F') (UU P P') - LinearMap.id) := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
    have hf : F.e i = F.fvec (Fin.castSucc i) := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [hf, sL_frame F F' hG P P', Fin.sum_univ_castSucc, (hPu _ _).1 (Fin.castSucc_lt_last i), zero_smul, add_zero,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i), (hPu _ _).2 rfl, one_smul, add_sub_cancel_right]
    refine Submodule.sum_mem _ fun c hc => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hci | hci
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_, ?_⟩)
      · show (c : ℕ) < j
        have : (c : ℕ) < i := hci
        simp only [Set.mem_setOf_eq] at hi
        omega
      · simp [Formalism.MainNotions.S.FlagG.fvec]
    · rw [(hPu _ _).1 (Fin.castSucc_lt_castSucc_iff.2 hci), zero_smul]
      exact Submodule.zero_mem _
  exact hle hx

theorem sL_Xa' (hG : IsUnit (gramOf (gg F F')).det) {P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hP'u : Formalism.MainNotions.S.IsUpUni P') (j : ℕ) (x : S.V) (hx : x ∈ F'.Xa (j + 1)) :
    sL (gg F F') (UU P P') x - x ∈ F'.Xa j := by
  have hle : F'.Xa (j + 1) ≤ (F'.Xa j).comap (sL (gg F F') (UU P P') - LinearMap.id) := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
    have hf : F'.e i = F'.fvec (Fin.castSucc i) := by simp [Formalism.MainNotions.S.FlagG.fvec]
    rw [hf, sL_frame' F F' hG P P', Fin.sum_univ_castSucc, (hP'u _ _).1 (Fin.castSucc_lt_last i), zero_smul, add_zero,
      ← Finset.sum_erase_add _ _ (Finset.mem_univ i), (hP'u _ _).2 rfl, one_smul, add_sub_cancel_right]
    refine Submodule.sum_mem _ fun c hc => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hci | hci
    · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, ?_, ?_⟩)
      · show (c : ℕ) < j
        have : (c : ℕ) < i := hci
        simp only [Set.mem_setOf_eq] at hi
        omega
      · simp [Formalism.MainNotions.S.FlagG.fvec]
    · rw [(hP'u _ _).1 (Fin.castSucc_lt_castSucc_iff.2 hci), zero_smul]
      exact Submodule.zero_mem _
  exact hle hx

end Orth

section LatInv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sL_lat (g : ι → S.V) (Λ : Submodule (𝓞 E) S.V) (X : Matrix ι ι E) {mc mg : ℕ} (hmc0 : mc ≠ 0)
    (hmg0 : mg ≠ 0) (hmc : ∀ v ∈ Λ, ∀ k, IntE ((mc : E) * coordL g k v)) (hmg : ∀ m, (mg : E) • g m ∈ Λ)
    (hX : ∀ m k, IntE ((X - 1) m k / ((mc * mg : ℕ) : E))) : ∀ v ∈ Λ, sL g X v ∈ Λ := by
  intro v hv
  rw [sL_apply]
  refine Λ.add_mem hv (Submodule.sum_mem _ fun m _ => ?_)
  have hmcE : (mc : E) ≠ 0 := Nat.cast_ne_zero.2 hmc0
  have hmgE : (mg : E) ≠ 0 := Nat.cast_ne_zero.2 hmg0
  have e : ((X - 1) *ᵥ cOf g v) m =
      (mg : E) * ∑ k, ((X - 1) m k / ((mc * mg : ℕ) : E)) * ((mc : E) * coordL g k v) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, cOf]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  rw [e, mul_smul]
  have ho : IntE (∑ k, ((X - 1) m k / ((mc * mg : ℕ) : E)) * ((mc : E) * coordL g k v)) :=
    intE_sum _ _ fun k _ => intE_mul (hX m k) (hmc v hv k)
  rw [smul_comm]
  exact int_smul_mem Λ ho (hmg m)

end LatInv

section IntMat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def SI (k : ℕ) (A : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, IntE ((k : E) * A i j)

theorem intE_inv_of {A : Matrix (Fin n) (Fin n) E} (hdet : A.det = 1) (hint : ∀ i j, IntE (A i j)) :
    ∀ i j, IntE (A⁻¹ i j) := by
  choose B hB using hint
  have hA : A = (algebraMap (𝓞 E) E).mapMatrix (Matrix.of B) := by
    ext i j; exact (hB i j).symm
  have hinv : A⁻¹ = A.adjugate := by rw [Matrix.inv_def, hdet, Ring.inverse_one, one_smul]
  intro i j
  rw [hinv, hA, ← RingHom.map_adjugate]
  exact ⟨(Matrix.of B).adjugate i j, rfl⟩

theorem div_int {k q Q : ℕ} {Y : Matrix (Fin n) (Fin n) E} (hY : SI k Y) (hq : q ≠ 0) :
    ∀ i j, IntE ((((q * k * Q : ℕ) : E) • Y) i j / (q : E)) := by
  intro i j
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e : (((q * k * Q : ℕ) : E) • Y) i j / (q : E) = (Q : E) * ((k : E) * Y i j) := by
    rw [Matrix.smul_apply, smul_eq_mul]; push_cast; field_simp
  rw [e]; exact intE_nat_mul Q (hY i j)

theorem div_int_conj {k q Q : ℕ} {Y : Matrix (Fin n) (Fin n) E} (hY : SI k Y) (hq : q ≠ 0) :
    ∀ i j, IntE (((((q * k * Q : ℕ) : E) • Y).conjTranspose) i j / (q : E)) := by
  intro i j
  rw [Matrix.conjTranspose_apply]
  have h := intE_star (div_int hY hq (Q := Q) j i)
  rwa [star_div₀, star_natCast] at h

end IntMat

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal

theorem volume_index_b_congruence (D : D7) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) :
    BCong D u u' F0 what₂ δ M := by
  intro hyps _ t w F' L U _ _ hN hG
  obtain ⟨_, _, hL, hU, hZ⟩ := hN
  have hlat : Submodule.IsLattice D.host.E t.lam := (hyps.2.2.2.2.2.1 t.lam t.mem).1.1
  set Z : MatR D := Zhat F0 F'.fl with hZdef
  have hZ1 : Z * sgnM D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact hZ
  have hLi : L⁻¹ * L = 1 := nonsing_inv_mul _ (by rw [lo_det hL]; exact isUnit_one)
  have hLL : L * L⁻¹ = 1 := mul_nonsing_inv _ (by rw [lo_det hL]; exact isUnit_one)
  have hUi : U * U⁻¹ = 1 := mul_nonsing_inv _ (by rw [up_det hU]; exact isUnit_one)
  have hZe : Z = L * ptMat w * U * sgnM D.R.rS := by
    rw [← hZ1, Matrix.mul_assoc, sgnM_sq, Matrix.mul_one]
  have hZu : IsUnit Z.det := by
    rw [isUnit_iff_ne_zero, hZe, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, lo_det hL, up_det hU, one_mul,
      mul_one]
    refine mul_ne_zero (ptMat_det w) ?_
    intro h0
    have := congrArg Matrix.det (sgnM_sq (K := D.host.E) (r := D.R.rS))
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hZi : Z⁻¹ * Z = 1 := nonsing_inv_mul _ hZu
  have hZZ : Z * Z⁻¹ = 1 := mul_nonsing_inv _ hZu
  have hZtu : IsUnit Z.conjTranspose.det := by rw [Matrix.det_conjTranspose]; exact hZu.star
  have hGr : IsUnit (gramOf (gg F0 F'.fl)).det :=
    gram_gg_unit F0 F'.fl (star_natCast _) (star_natCast _) hZu hG

  obtain ⟨mc, hmc0, hmc⟩ := lat_fun_bdd t.lam hlat (coordL (gg F0 F'.fl))
  have hmgm : ∀ m, ∃ k : ℕ, k ≠ 0 ∧ (k : D.host.E) • gg F0 F'.fl m ∈ t.lam := fun m => lat_smul_mem t.lam hlat _
  choose mm hmm0 hmmL using hmgm
  set mg : ℕ := ∏ m, mm m with hmg
  have hmg0 : mg ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hmm0 m
  have hmgL : ∀ m, (mg : D.host.E) • gg F0 F'.fl m ∈ t.lam := by
    intro m
    have : (mg : D.host.E) • gg F0 F'.fl m =
        ((∏ j ∈ Finset.univ.erase m, mm j : ℕ) : D.host.E) • ((mm m : D.host.E) • gg F0 F'.fl m) := by
      rw [smul_smul, hmg, ← Finset.mul_prod_erase Finset.univ mm (Finset.mem_univ m)]; push_cast; ring_nf
    rw [this]; exact nat_smul_mem _ _ (hmmL m)
  obtain ⟨dL, hdL0, hdL⟩ := den_mat L
  obtain ⟨dLi, hdLi0, hdLi⟩ := den_mat L⁻¹
  obtain ⟨dZ, hdZ0, hdZ⟩ := den_mat Z
  obtain ⟨dZi, hdZi0, hdZi⟩ := den_mat Z⁻¹
  set q := mc * mg with hq
  have hq0 : q ≠ 0 := mul_ne_zero hmc0 hmg0
  set k1 := dL * 1 * dLi with hk1
  set k2 := dZi * (dL * 1 * dLi) * dZ with hk2
  set N := q * k1 * k2 with hNdef
  have hN0 : N ≠ 0 := by
    simp only [hNdef, hk1, hk2]
    exact mul_ne_zero (mul_ne_zero hq0 (by positivity)) (by positivity)
  have hNE : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hN2 : ((N : ℕ) : D.host.E) = ((q * k2 * k1 : ℕ) : D.host.E) := by congr 1; simp only [hNdef]; ring
  refine ⟨N, hN0, ?_⟩
  intro a ha hcong
  obtain ⟨haLo, b, hbUp, hab⟩ := ha
  set A : MatR D := (a : MatR D) with hAdef

  set X0 : MatR D := fun i j => (A i j - (1 : MatR D) i j) / (N : D.host.E) with hX0def
  have hX0 : SI 1 X0 := fun i j => by rw [Nat.cast_one, one_mul]; exact hcong i j
  have hA1 : A - 1 = (N : D.host.E) • X0 := by
    funext i j
    show A i j - (1 : MatR D) i j = (N : D.host.E) * ((A i j - (1 : MatR D) i j) / (N : D.host.E))
    field_simp
  have hAint : ∀ i j, IntE (A i j) := by
    intro i j
    have e : A i j = (1 : MatR D) i j + (N : D.host.E) * X0 i j := by
      have := congrFun (congrFun hA1 i) j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this
      rw [← this]; ring
    rw [e]
    refine intE_add ?_ (intE_nat_mul N (by simpa using hX0 i j))
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact intE_one
    · rw [Matrix.one_apply_ne hij]; exact intE_zero
  have hAdet : A.det = 1 := lo_det haLo
  have hAu : IsUnit A.det := by rw [hAdet]; exact isUnit_one
  have hAiA : A⁻¹ * A = 1 := nonsing_inv_mul _ hAu
  have hAAi : A * A⁻¹ = 1 := mul_nonsing_inv _ hAu
  have hAiint : SI 1 A⁻¹ := fun i j => by rw [Nat.cast_one, one_mul]; exact intE_inv_of hAdet hAint i j
  set X1 : MatR D := -(A⁻¹ * X0) with hX1def
  have hX1 : SI 1 X1 := fun i j => by
    have h := intE_matmul hAiint hX0 i j
    rw [Nat.cast_mul, Nat.cast_one, one_mul] at h
    rw [Nat.cast_one, one_mul, hX1def, Matrix.neg_apply]
    exact intE_neg (by simpa using h)
  have hAi1 : A⁻¹ - 1 = (N : D.host.E) • X1 := by
    have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by rw [Matrix.mul_sub, hAiA, Matrix.mul_one]; abel
    rw [e, hA1, Matrix.mul_smul, hX1def, smul_neg]

  have hLAL : IsLoUni (L * A * L⁻¹) := lo_mul (lo_mul hL haLo) (lo_inv hL)
  have hLAiL : IsLoUni (L * A⁻¹ * L⁻¹) := lo_mul (lo_mul hL (lo_inv haLo)) (lo_inv hL)
  set P : MatR D := (L * A * L⁻¹).conjTranspose with hPdef
  set Pinv : MatR D := (L * A⁻¹ * L⁻¹).conjTranspose with hPinvdef
  set P' : MatR D := Z⁻¹ * (L * A⁻¹ * L⁻¹) * Z with hP'def
  set P'inv : MatR D := Z⁻¹ * (L * A * L⁻¹) * Z with hP'invdef
  have hPu : IsUpUni P := up_conjT hLAL
  have hwb : ptMat w * b = A⁻¹ * ptMat w := by
    have := congrArg (fun X => A⁻¹ * X) hab
    simp only [← Matrix.mul_assoc, hAiA, Matrix.one_mul] at this
    exact this
  have key : Z * (sgnM D.R.rS * (U⁻¹ * b * U) * sgnM D.R.rS) = L * A⁻¹ * L⁻¹ * Z := by
    have h1 : ∀ X : MatR D, sgnM D.R.rS * (sgnM D.R.rS * X) = X := fun X => by
      rw [← Matrix.mul_assoc, sgnM_sq, Matrix.one_mul]
    have h2 : ∀ X : MatR D, U * (U⁻¹ * X) = X := fun X => by rw [← Matrix.mul_assoc, hUi, Matrix.one_mul]
    have h3 : ∀ X : MatR D, L⁻¹ * (L * X) = X := fun X => by rw [← Matrix.mul_assoc, hLi, Matrix.one_mul]
    have h4 : ∀ X : MatR D, ptMat w * (b * X) = A⁻¹ * (ptMat w * X) := fun X => by
      rw [← Matrix.mul_assoc, hwb, Matrix.mul_assoc]
    rw [hZe]
    simp only [Matrix.mul_assoc, h1, h2, h3, h4]
  have hP'eq : P' = sgnM D.R.rS * (U⁻¹ * b * U) * sgnM D.R.rS := by
    rw [hP'def, Matrix.mul_assoc, ← key, ← Matrix.mul_assoc, hZi, Matrix.one_mul]
  have hP'u : IsUpUni P' := by rw [hP'eq]; exact up_sgn (up_mul (up_mul (up_inv hU) hbUp) hU)
  have hPP : P * Pinv = 1 := by
    rw [hPdef, hPinvdef, ← Matrix.conjTranspose_mul]
    have : L * A⁻¹ * L⁻¹ * (L * A * L⁻¹) = 1 := by
      calc L * A⁻¹ * L⁻¹ * (L * A * L⁻¹) = L * (A⁻¹ * ((L⁻¹ * L) * A)) * L⁻¹ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLi, Matrix.one_mul, hAiA, Matrix.mul_one, hLL]
    rw [this, Matrix.conjTranspose_one]
  have hPP' : Pinv * P = 1 := by
    rw [hPdef, hPinvdef, ← Matrix.conjTranspose_mul]
    have : L * A * L⁻¹ * (L * A⁻¹ * L⁻¹) = 1 := by
      calc L * A * L⁻¹ * (L * A⁻¹ * L⁻¹) = L * (A * ((L⁻¹ * L) * A⁻¹)) * L⁻¹ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLi, Matrix.one_mul, hAAi, Matrix.mul_one, hLL]
    rw [this, Matrix.conjTranspose_one]
  have hQQ : P' * P'inv = 1 := by
    calc P' * P'inv = Z⁻¹ * (L * (A⁻¹ * ((L⁻¹ * (Z * Z⁻¹) * L) * A)) * L⁻¹) * Z := by
          simp only [hP'def, hP'invdef, Matrix.mul_assoc]
      _ = 1 := by rw [hZZ, Matrix.mul_one, hLi, Matrix.one_mul, hAiA, Matrix.mul_one, hLL, Matrix.mul_one, hZi]
  have hQQ' : P'inv * P' = 1 := by
    calc P'inv * P' = Z⁻¹ * (L * (A * ((L⁻¹ * (Z * Z⁻¹) * L) * A⁻¹)) * L⁻¹) * Z := by
          simp only [hP'def, hP'invdef, Matrix.mul_assoc]
      _ = 1 := by rw [hZZ, Matrix.mul_one, hLi, Matrix.one_mul, hAAi, Matrix.mul_one, hLL, Matrix.mul_one, hZi]
  have hZrel : P.conjTranspose * Z * P' = Z := by
    rw [hPdef, Matrix.conjTranspose_conjTranspose, hP'def]
    calc L * A * L⁻¹ * Z * (Z⁻¹ * (L * A⁻¹ * L⁻¹) * Z) = L * (A * ((L⁻¹ * ((Z * Z⁻¹) * L)) * A⁻¹)) * L⁻¹ * Z := by
          simp only [Matrix.mul_assoc]
      _ = Z := by rw [hZZ, Matrix.one_mul, hLi, Matrix.one_mul, hAAi, Matrix.mul_one, hLL, Matrix.one_mul]
  have hPHinv : (P.conjTranspose)⁻¹ = L * A⁻¹ * L⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hPdef, Matrix.conjTranspose_conjTranspose]
    calc L * A⁻¹ * L⁻¹ * (L * A * L⁻¹) = L * (A⁻¹ * ((L⁻¹ * L) * A)) * L⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hLi, Matrix.one_mul, hAiA, Matrix.mul_one, hLL]
  have hrel : P' = Z⁻¹ * (P.conjTranspose)⁻¹ * Z := by rw [hPHinv]
  have hPl : IsLoUni (P.conjTranspose)⁻¹ := by rw [hPHinv]; exact hLAiL
  have hP'Hinv : (P'.conjTranspose)⁻¹ = P'inv.conjTranspose := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
  have hP'inv_eq : P'⁻¹ = P'inv := Matrix.inv_eq_left_inv hQQ'
  have hP'l : IsLoUni (P'.conjTranspose)⁻¹ := by
    rw [hP'Hinv, ← hP'inv_eq]; exact lo_conjT (up_inv hP'u)
  have hZtZ : ((Z.conjTranspose)⁻¹) * Z.conjTranspose = 1 := nonsing_inv_mul _ hZtu
  have hrel' : P = (Z.conjTranspose)⁻¹ * (P'.conjTranspose)⁻¹ * Z.conjTranspose := by
    rw [hP'Hinv, hP'invdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    have hZc : (Z⁻¹).conjTranspose * Z.conjTranspose = 1 := by
      rw [← Matrix.conjTranspose_mul, hZZ, Matrix.conjTranspose_one]
    calc P = ((Z.conjTranspose)⁻¹ * Z.conjTranspose) * P * ((Z⁻¹).conjTranspose * Z.conjTranspose) := by
          rw [hZtZ, hZc, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [hPdef]; simp only [Matrix.mul_assoc]

  have hUU1 : UU P P' * UU Pinv P'inv = 1 := by rw [UU_mul, hPP, hQQ, UU_one]
  have hUU2 : UU Pinv P'inv * UU P P' = 1 := by rw [UU_mul, hPP', hQQ', UU_one]
  set sg := sE (gg F0 F'.fl) hGr (UU P P') (UU Pinv P'inv) hUU1 hUU2 with hsg
  have hsi : ∀ x y, (VS D).hT (sg x) (sg y) = (VS D).hT x y :=
    sL_isom (gg F0 F'.fl) hGr (UU P P') (UU_isom F0 F'.fl hPu hP'u hZrel)

  have hLX0 : SI k1 (L * X0 * L⁻¹) := intE_matmul (intE_matmul hdL hX0) hdLi
  have hLX1 : SI k1 (L * X1 * L⁻¹) := intE_matmul (intE_matmul hdL hX1) hdLi
  have hZX0 : SI k2 (Z⁻¹ * (L * X0 * L⁻¹) * Z) := intE_matmul (intE_matmul hdZi hLX0) hdZ
  have hZX1 : SI k2 (Z⁻¹ * (L * X1 * L⁻¹) * Z) := intE_matmul (intE_matmul hdZi hLX1) hdZ
  have eP : P - 1 = (((q * k1 * k2 : ℕ) : D.host.E) • (L * X0 * L⁻¹)).conjTranspose := by
    rw [hPdef, ← Matrix.conjTranspose_one, ← Matrix.conjTranspose_sub]
    congr 1
    rw [← hLL, show L * A * L⁻¹ - L * L⁻¹ = L * (A - 1) * L⁻¹ by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one], hA1, Matrix.mul_smul, Matrix.smul_mul]
  have ePi : Pinv - 1 = (((q * k1 * k2 : ℕ) : D.host.E) • (L * X1 * L⁻¹)).conjTranspose := by
    rw [hPinvdef, ← Matrix.conjTranspose_one, ← Matrix.conjTranspose_sub]
    congr 1
    rw [← hLL, show L * A⁻¹ * L⁻¹ - L * L⁻¹ = L * (A⁻¹ - 1) * L⁻¹ by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one], hAi1, Matrix.mul_smul, Matrix.smul_mul]
  have eP' : P' - 1 = ((q * k2 * k1 : ℕ) : D.host.E) • (Z⁻¹ * (L * X1 * L⁻¹) * Z) := by
    rw [hP'def, conj_sub_one hZu, ← hLL, show L * A⁻¹ * L⁻¹ - L * L⁻¹ = L * (A⁻¹ - 1) * L⁻¹ by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one], hAi1, ← hN2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have eP'i : P'inv - 1 = ((q * k2 * k1 : ℕ) : D.host.E) • (Z⁻¹ * (L * X0 * L⁻¹) * Z) := by
    rw [hP'invdef, conj_sub_one hZu, ← hLL, show L * A * L⁻¹ - L * L⁻¹ = L * (A - 1) * L⁻¹ by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one], hA1, ← hN2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul]
  have hXUU : ∀ m k, IntE ((UU P P' - 1) m k / ((mc * mg : ℕ) : D.host.E)) := by
    rw [UU_sub_one]
    rintro (i | i) (j | j)
    · simp only [Matrix.fromBlocks_apply₁₁]; rw [eP]; exact div_int_conj hLX0 hq0 i j
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_div]; exact intE_zero
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_div]; exact intE_zero
    · simp only [Matrix.fromBlocks_apply₂₂]; rw [eP']; exact div_int hZX1 hq0 i j
  have hXUU' : ∀ m k, IntE ((UU Pinv P'inv - 1) m k / ((mc * mg : ℕ) : D.host.E)) := by
    rw [UU_sub_one]
    rintro (i | i) (j | j)
    · simp only [Matrix.fromBlocks_apply₁₁]; rw [ePi]; exact div_int_conj hLX1 hq0 i j
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_div]; exact intE_zero
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_div]; exact intE_zero
    · simp only [Matrix.fromBlocks_apply₂₂]; rw [eP'i]; exact div_int hZX0 hq0 i j
  have hin := sL_lat (gg F0 F'.fl) t.lam (UU P P') hmc0 hmg0 hmc hmgL hXUU
  have hin' := sL_lat (gg F0 F'.fl) t.lam (UU Pinv P'inv) hmc0 hmg0 hmc hmgL hXUU'
  have hsΛ : Formalism.HermitianLatticesTheory.gmap sg t.lam = t.lam := by
    ext x
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
    constructor
    · intro hx
      have := hin _ hx
      rwa [show sL (gg F0 F'.fl) (UU P P') (sg.symm x) = sg (sg.symm x) from rfl, LinearEquiv.apply_symm_apply] at this
    · intro hx; exact hin' x hx
  have hAut : IsAutLam (VS D) t.lam sg := ⟨hsi, hsΛ⟩

  have hN1 : sg ∈ NLam t.lam (lf D F0) := by
    refine ⟨hAut, fun j x hx => sL_Xa F0 F'.fl hGr hPu j x hx, fun x hx => ?_⟩
    have hx0 : ∀ a : Fin D.R.rS, (VS D).hT (F0.e a) x = 0 := fun a =>
      (Formalism.L2.SG.Pf.mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    exact sL_orth F0 F'.fl hGr hPu hZu hrel hPl x hx0
  have hN2' : sg ∈ NLam t.lam F' := by
    refine ⟨hAut, fun j x hx => sL_Xa' F0 F'.fl hGr hP'u j x hx, fun x hx => ?_⟩
    have hx0 : ∀ a : Fin D.R.rS, (VS D).hT (F'.fl.e a) x = 0 := fun a =>
      (Formalism.L2.SG.Pf.mem_orth' _ x).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
    exact sL_orth' F0 F'.fl hGr hP'u hZtu hrel' hP'l x hx0
  refine Subgroup.subset_closure ⟨sg, ⟨hN1, hN2'⟩, P, fun b => ?_, ?_⟩
  · exact sL_frame F0 F'.fl hGr P P' b
  · show A = L⁻¹ * P.conjTranspose * L
    rw [hPdef, Matrix.conjTranspose_conjTranspose]
    calc A = (L⁻¹ * L) * A * (L⁻¹ * L) := by rw [hLi, Matrix.one_mul, Matrix.mul_one]
      _ = L⁻¹ * (L * A * L⁻¹) * L := by simp only [Matrix.mul_assoc]

end Main

end Formalism.L2.SG.Pf.StabilizerIndexVolumes
