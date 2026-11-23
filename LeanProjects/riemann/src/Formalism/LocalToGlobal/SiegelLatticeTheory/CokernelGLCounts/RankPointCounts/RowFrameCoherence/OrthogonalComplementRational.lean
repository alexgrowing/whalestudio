import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO1FrameValPiIso
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux

open Module

open scoped Matrix

theorem rank_le_rank_map {K L : Type*} [Field K] [Field L] (φ : K →+* L) {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n K) : A.rank ≤ (A.map φ).rank := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have hbfin : b.Finite := (Set.finite_range _).subset hbs
  haveI := hbfin.fintype
  have h1 : finrank K (Submodule.span K (Set.range A.col)) = Fintype.card b := by
    rw [← hspan, finrank_span_set_eq_card hli, Set.toFinset_card]
  have hli' : LinearIndependent L (fun i : b => algebraMap K L ∘ (i : m → K)) :=
    linearIndependent_algebraMap_comp_iff.2 hli
  have hsub : Set.range (fun i : b => algebraMap K L ∘ (i : m → K)) ⊆ Set.range (A.map φ).col := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨j, rfl⟩ := hbs hx
    refine ⟨j, ?_⟩
    funext i
    simp [Matrix.col_apply, Matrix.map_apply, RingHom.algebraMap_toAlgebra]
  calc finrank K (Submodule.span K (Set.range A.col)) = Fintype.card b := h1
    _ = finrank L (Submodule.span L (Set.range (fun i : b => algebraMap K L ∘ (i : m → K)))) :=
        (finrank_span_eq_card hli').symm
    _ ≤ _ := Submodule.finrank_mono (Submodule.span_mono hsub)

theorem ker_map_le_span {K L : Type*} [Field K] [Field L] (φ : K →+* L) {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n K) (z : n → L) (hz : (A.map φ) *ᵥ z = 0) :
    z ∈ Submodule.span L ((fun x : n → K => φ ∘ x) '' {x | A *ᵥ x = 0}) := by
  letI := φ.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 φ.injective
  set S := LinearMap.ker A.mulVecLin
  let bS := Module.finBasis K S
  let w : Fin (finrank K S) → n → L := fun i => algebraMap K L ∘ ((bS i : S) : n → K)
  have hli0 : LinearIndependent K (fun i => ((bS i : S) : n → K)) :=
    bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hw : LinearIndependent L w := linearIndependent_algebraMap_comp_iff.2 hli0
  have hmap : ∀ x : n → K, (A.map φ) *ᵥ (φ ∘ x) = φ ∘ (A *ᵥ x) := by
    intro x
    funext k
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  have hT : Submodule.span L (Set.range w) ≤ LinearMap.ker (A.map φ).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hx : A *ᵥ ((bS i : S) : n → K) = 0 := (bS i).2
    show (A.map φ) *ᵥ w i = 0
    have : w i = φ ∘ ((bS i : S) : n → K) := by
      funext k
      simp [w, RingHom.algebraMap_toAlgebra]
    rw [this, hmap, hx]
    funext k
    simp
  have hdim : finrank L (LinearMap.ker (A.map φ).mulVecLin) ≤ finrank L (Submodule.span L (Set.range w)) := by
    rw [finrank_span_eq_card hw, Fintype.card_fin]
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 := LinearMap.finrank_range_add_finrank_ker (A.map φ).mulVecLin
    have h3 := rank_le_rank_map φ A
    unfold Matrix.rank at h3
    rw [Module.finrank_fintype_fun_eq_card] at h1 h2
    have hS : finrank K S = finrank K (LinearMap.ker A.mulVecLin) := rfl
    rw [hS]
    omega
  have heq := Submodule.eq_of_le_of_finrank_le hT hdim
  have hz' : z ∈ LinearMap.ker (A.map φ).mulVecLin := hz
  rw [← heq] at hz'
  refine Submodule.span_mono ?_ hz'
  rintro _ ⟨i, rfl⟩
  refine ⟨((bS i : S) : n → K), (bS i).2, ?_⟩
  funext k
  simp [w, RingHom.algebraMap_toAlgebra]

section Coord

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem hJ_swap' {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem hJ_add_right {n : ℕ} (ε : Fin n → Bool) (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  unfold hJ; rw [Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul_right {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero_right {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  unfold hJ; simp

theorem wCoord_add {n k : ℕ} (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) (y y' : Fin n → ℂ) :
    Formalism.L2.SG.RealObj.wCoord ε wb (y + y') = Formalism.L2.SG.RealObj.wCoord ε wb y + Formalism.L2.SG.RealObj.wCoord ε wb y' := by
  funext i; simp [Formalism.L2.SG.RealObj.wCoord, hJ_add_right]

theorem wCoord_smul {n k : ℕ} (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) :
    Formalism.L2.SG.RealObj.wCoord ε wb (c • y) = c • Formalism.L2.SG.RealObj.wCoord ε wb y := by
  funext i; simp [Formalism.L2.SG.RealObj.wCoord, hJ_smul_right]

theorem wCoord_zero {n k : ℕ} (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) :
    Formalism.L2.SG.RealObj.wCoord ε wb 0 = 0 := by
  funext i; simp [Formalism.L2.SG.RealObj.wCoord, hJ_zero_right]

def famE (w : D.what₂.Word) : Fin (D.R.rS + 1) → Fin X.B.I.n → X.B.I.E :=
  Fin.snoc (α := fun _ => Fin X.B.I.n → X.B.I.E) X.eR (X.zR w)

theorem frm_one (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.frm X w 1 v = fun a => rv X.B.I v (famE X w a) := by
  funext a
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam famE
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

def WperpE (w : D.what₂.Word) : Submodule X.B.I.E (Fin X.B.I.n → X.B.I.E) :=
  Submodule.span X.B.I.E (Set.range X.eR ∪ Set.range X.fR ∪ {X.zR w})

theorem rv_add' (v : NumberField.InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (x + y) = rv X.B.I v x + rv X.B.I v y :=
  map_add (Formalism.L2.SG.Pf.Level.rvHom X v) x y

theorem rv_sub' (v : NumberField.InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (x - y) = rv X.B.I v x - rv X.B.I v y :=
  map_sub (Formalism.L2.SG.Pf.Level.rvHom X v) x y

theorem rv_smul'' (v : NumberField.InfinitePlace X.B.I.F) (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (c • x) = X.B.I.φ v c • rv X.B.I v x :=
  Formalism.L2.SG.Pf.Level.rv_smul X v c x

theorem rv_sum' {ι : Type*} (s : Finset ι) (v : NumberField.InfinitePlace X.B.I.F) (x : ι → Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (∑ i ∈ s, x i) = ∑ i ∈ s, rv X.B.I v (x i) :=
  map_sum (Formalism.L2.SG.Pf.Level.rvHom X v) x s

theorem rv_zero' (v : NumberField.InfinitePlace X.B.I.F) : rv X.B.I v 0 = 0 :=
  map_zero (Formalism.L2.SG.Pf.Level.rvHom X v)

theorem wCoord_perp (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) (x : Fin X.B.I.n → X.B.I.E)
    (hx : x ∈ WperpE X w) : Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr w v) (rv X.B.I v x) = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    funext i
    show hJ (X.B.I.ε v) (X.wfr w v i) (rv X.B.I v y) = 0
    rw [hJ_swap']
    have hp := X.wfr_perp w v i
    rcases hy with (⟨c, rfl⟩ | ⟨c, rfl⟩) | hz
    · rw [show hJ (X.B.I.ε v) (rv X.B.I v (X.eR c)) (X.wfr w v i) = 0 from (hp.1 c).1, star_zero]
    · rw [show hJ (X.B.I.ε v) (rv X.B.I v (X.fR c)) (X.wfr w v i) = 0 from (hp.1 c).2, star_zero]
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [show hJ (X.B.I.ε v) (rv X.B.I v (X.zR w)) (X.wfr w v i) = 0 from hp.2, star_zero]
  | zero => rw [rv_zero', wCoord_zero]
  | add x y _ _ hx hy => rw [rv_add', wCoord_add, hx, hy, add_zero]
  | smul c x _ hx => rw [rv_smul'', wCoord_smul, hx, smul_zero]

theorem wCoord_eq_of_perp (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) (x y : Fin X.B.I.n → X.B.I.E)
    (h : x - y ∈ WperpE X w) :
    Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr w v) (rv X.B.I v x) =
      Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr w v) (rv X.B.I v y) := by
  have h0 := wCoord_perp X w v _ h
  rw [rv_sub', show rv X.B.I v x - rv X.B.I v y = rv X.B.I v x + (-1 : ℂ) • rv X.B.I v y by
    rw [neg_one_smul, sub_eq_add_neg], wCoord_add, wCoord_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0

end Coord

section Real

variable {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

def ZE (u u' : D.what₂.Word) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) X.B.I.E :=
  fun a b => Formalism.L2.SG.Pf.Level.hE X (famE X u a) (M *ᵥ famE X u' b)

def xPrE (u u' : D.what₂.Word) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  ∑ b, (ZE X u u' M).adjugate b (Fin.last _) • (M *ᵥ famE X u' b)

def xUnE (u u' : D.what₂.Word) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  ∑ a, star ((ZE X u u' M).adjugate (Fin.last _) a) • famE X u a

def nu1E (u u' : D.what₂.Word) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  ((ZE X u u' M).det)⁻¹ • xPrE X u u' M

def nu2E (u u' : D.what₂.Word) (M Mi : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  (star (ZE X u u' M).det)⁻¹ • (Mi *ᵥ xUnE X u u' M)

def orthogonalComplementRational (u u' : D.what₂.Word) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) : Prop :=
  (∀ a, Formalism.L2.SG.Pf.Level.hE X (famE X u a) y = 0) ∧ ∀ b, Formalism.L2.SG.Pf.Level.hE X (M *ᵥ famE X u' b) y = 0

variable (u u' : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)

abbrev rl (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ :=
  (X.B.I.P v)⁻¹ * M.map (X.B.I.φ v) * X.B.I.P v

theorem zhat_rat (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Formalism.L2.SG.RealObj.Zhat (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v) (rl X v M) =
      (ZE X u u' M).map (X.B.I.φ v) := by
  ext a b
  rw [frm_one, frm_one]
  simp only [Formalism.L2.SG.RealObj.Zhat, Matrix.map_apply, ZE]
  rw [Formalism.L2.SG.Pf.Level.rv_mulVec, Formalism.L2.SG.Pf.Level.hJ_rv]

theorem dl_rat (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) X.B.I.E) :
    Formalism.L2.SG.RealObj.Dl (Z.map (X.B.I.φ v)) (D.R.rS + 1) = X.B.I.φ v Z.det := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dif_pos le_rfl, RingHom.map_det]
  congr 1

theorem adj_rat (Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) X.B.I.E) :
    (Z.map (X.B.I.φ v)).adjugate = Z.adjugate.map (X.B.I.φ v) :=
  (RingHom.map_adjugate (X.B.I.φ v) Z).symm

theorem xPr_rat (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Formalism.L2.SG.RealObj.xPr ((ZE X u u' M).map (X.B.I.φ v)) (rl X v M) (Formalism.L2.SG.RealObj.frm X u' 1 v) =
      rv X.B.I v (xPrE X u u' M) := by
  unfold Formalism.L2.SG.RealObj.xPr xPrE
  rw [adj_rat, frm_one, rv_sum']
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rv_smul'', Formalism.L2.SG.Pf.Level.rv_mulVec, Matrix.map_apply]

theorem xUn_rat (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Formalism.L2.SG.RealObj.xUn ((ZE X u u' M).map (X.B.I.φ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) =
      rv X.B.I v (xUnE X u u' M) := by
  unfold Formalism.L2.SG.RealObj.xUn xUnE
  rw [adj_rat, frm_one, rv_sum']
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rv_smul'', Matrix.map_apply, Formalism.L2.SG.Pf.Level.phi_star]

theorem wCoord_rvsmul {k : ℕ} (wb : Fin k → Fin X.B.I.n → ℂ) (c : X.B.I.E) (x : Fin X.B.I.n → X.B.I.E) :
    X.B.I.φ v c • Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) wb (rv X.B.I v x) =
      Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) wb (rv X.B.I v (c • x)) := by
  rw [rv_smul'', wCoord_smul]

theorem firstNormal_rational (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    ClassFrameUnitaryProducts.nrm1 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v) (rl X v M)
        (X.wfr u v) = Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) (rv X.B.I v (nu1E X u u' M)) := by
  unfold ClassFrameUnitaryProducts.nrm1 nu1E
  rw [zhat_rat, dl_rat, xPr_rat, ← map_inv₀, wCoord_rvsmul]

theorem secondNormal_rational (M Mi : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    ClassFrameUnitaryProducts.nrm2 (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v) (Formalism.L2.SG.RealObj.frm X u' 1 v) (rl X v M)
        (rl X v Mi) (X.wfr u' v) = Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (rv X.B.I v (nu2E X u u' M Mi)) := by
  unfold ClassFrameUnitaryProducts.nrm2 nu2E
  rw [zhat_rat, dl_rat, xUn_rat, Formalism.L2.SG.Pf.Level.rv_mulVec, ← Formalism.L2.SG.Pf.Level.phi_star, ← map_inv₀,
    wCoord_rvsmul]

end Real

end Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def ratM (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    GL (Fin X.B.I.n) X.B.I.E :=
  s.rep.2.1.choose

theorem uMat_ratM (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (v : NumberField.InfinitePlace X.B.I.F) :
    uMat (s.pt.1 v) = rl X v ((ratM X Y u u' s : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :=
  s.rep.2.1.choose_spec.2.1 v

theorem uMat_inv_ratM (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (v : NumberField.InfinitePlace X.B.I.F) :
    uMat ((s.pt.1 v)⁻¹) =
      rl X v (((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have h1 : uMat ((s.pt.1 v)⁻¹) * uMat (s.pt.1 v) = 1 := Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' _
  have e : ((((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (X.B.I.φ v)) * (((ratM X Y u u' s : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map
      (X.B.I.φ v)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : rl X v (((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      uMat (s.pt.1 v) = 1 := by
    rw [uMat_ratM]
    simp only [rl, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hPu, ← Matrix.mul_assoc (Matrix.map _ _), e, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hPu]
  have h3 : uMat (s.pt.1 v) * uMat ((s.pt.1 v)⁻¹) = 1 := mul_eq_one_comm.1 h1
  calc uMat ((s.pt.1 v)⁻¹) = (rl X v (((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * uMat (s.pt.1 v)) * uMat ((s.pt.1 v)⁻¹) := by rw [h2, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h3, Matrix.mul_one]

def ScalarAgreeRatC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s₁ s₂ : LiftT X Y u u' κ R ρ),
    s₁.1.relevant → s₂.1.relevant →
      nu1E X u u' (ratM X Y u u' s₁.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) -
          nu1E X u u' (ratM X Y u u' s₂.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) ∈ WperpE X u ∧
      nu2E X u u' (ratM X Y u u' s₁.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
            (((ratM X Y u u' s₁.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) -
          nu2E X u u' (ratM X Y u u' s₂.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
            (((ratM X Y u u' s₂.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) ∈ WperpE X u' ∧
      ∀ y₂, orthogonalComplementRational X u u' (ratM X Y u u' s₂.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y₂ →
        ∃ y₁, orthogonalComplementRational X u u' (ratM X Y u u' s₁.1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) y₁ ∧ y₁ - y₂ ∈ WperpE X u ∧
          (((ratM X Y u u' s₁.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y₁ -
            (((ratM X Y u u' s₂.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y₂ ∈
              WperpE X u'

end Formalism.L2.SG.Pf.RowForm

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem classFrameOO2_hE_expand (a x : Fin X.B.I.n → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.hE X a x = ∑ j, Formalism.L2.SG.Pf.Level.hE X a (Pi.single j 1) * x j := by
  conv_lhs => rw [← Formalism.L2.SG.Pf.Level.sum_single X x]
  rw [← Formalism.L2.SG.Pf.Level.hEl_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Formalism.L2.SG.Pf.Level.hEl_apply, smul_eq_mul, mul_comm]

theorem classFrameOO2_hJ_sum {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ_zero_right]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hJ_add_right, ih]

theorem classFrameOO2_hJ_expand (v : NumberField.InfinitePlace X.B.I.F) (a : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v a) y =
      ∑ j, X.B.I.φ v (Formalism.L2.SG.Pf.Level.hE X a (Pi.single j 1)) * (X.B.I.P v *ᵥ y) j := by
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hs1 : ∀ j, rv X.B.I v (Pi.single j 1) = (X.B.I.P v)⁻¹ *ᵥ Pi.single j 1 := by
    intro j
    unfold rv
    congr 1
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have hy : y = ∑ j, (X.B.I.P v *ᵥ y) j • rv X.B.I v (Pi.single j 1) := by
    simp only [hs1, ← Matrix.mulVec_smul, ← Matrix.mulVec_sum]
    rw [Formalism.L2.SG.Pf.Level.sum_single X, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mulVec]
  conv_lhs => rw [hy]
  rw [classFrameOO2_hJ_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ_smul_right, Formalism.L2.SG.Pf.Level.hJ_rv, mul_comm]

theorem scalarAgreeC_of_rat (hR : ScalarAgreeRatC X Y u u' κ) : ScalarAgreeC X Y u u' κ := by
  intro R ρ s₁ s₂ h₁ h₂ v
  obtain ⟨ha, hb, hc⟩ := hR R ρ s₁ s₂ h₁ h₂
  have hPu : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  rw [uMat_ratM X Y u u' s₁.1 v, uMat_ratM X Y u u' s₂.1 v, uMat_inv_ratM X Y u u' s₁.1 v, uMat_inv_ratM X Y u u' s₂.1 v]
  refine ⟨?_, ?_, ?_⟩
  · rw [firstNormal_rational, firstNormal_rational]
    exact wCoord_eq_of_perp X u v _ _ ha
  · rw [secondNormal_rational, secondNormal_rational]
    exact wCoord_eq_of_perp X u' v _ _ hb
  · intro y₂ hy₂a hy₂b
    set M₁ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
      ((ratM X Y u u' s₁.1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hM₁
    set M₂ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
      ((ratM X Y u u' s₂.1 : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hM₂
    set Mi₁ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
      (((ratM X Y u u' s₁.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hMi₁
    set Mi₂ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
      (((ratM X Y u u' s₂.1)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hMi₂
    let wv : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → Fin X.B.I.n → X.B.I.E :=
      Sum.elim (famE X u) (fun b => M₂ *ᵥ famE X u' b)
    let A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin X.B.I.n) X.B.I.E :=
      fun i j => Formalism.L2.SG.Pf.Level.hE X (wv i) (Pi.single j 1)
    have hA : ∀ x i, (A *ᵥ x) i = Formalism.L2.SG.Pf.Level.hE X (wv i) x := by
      intro x i
      rw [classFrameOO2_hE_expand X (wv i) x]
      rfl
    have hAc : (A.map (X.B.I.φ v)) *ᵥ (X.B.I.P v *ᵥ y₂) = 0 := by
      funext i
      have h0 : hJ (X.B.I.ε v) (rv X.B.I v (wv i)) y₂ = 0 := by
        rcases i with a | b
        · have := hy₂a a
          rw [frm_one] at this
          exact this
        · have := hy₂b b
          rw [frm_one, Formalism.L2.SG.Pf.Level.rv_mulVec] at this
          exact this
      rw [classFrameOO2_hJ_expand] at h0
      simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using h0
    have hspan := ClassFrameOO2Aux.ker_map_le_span (X.B.I.φ v) A _ hAc
    have key : ∀ z ∈ Submodule.span ℂ ((fun x : Fin X.B.I.n → X.B.I.E => X.B.I.φ v ∘ x) '' {x | A *ᵥ x = 0}),
        ∃ y₁ : Fin X.B.I.n → ℂ,
          (∀ a, hJ (X.B.I.ε v) (Formalism.L2.SG.RealObj.frm X u 1 v a) y₁ = 0) ∧
          (∀ b, hJ (X.B.I.ε v) (rl X v M₁ *ᵥ Formalism.L2.SG.RealObj.frm X u' 1 v b) y₁ = 0) ∧
          Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) y₁ =
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u v) ((X.B.I.P v)⁻¹ *ᵥ z) ∧
          Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (rl X v Mi₁ *ᵥ y₁) =
            Formalism.L2.SG.RealObj.wCoord (X.B.I.ε v) (X.wfr u' v) (rl X v Mi₂ *ᵥ ((X.B.I.P v)⁻¹ *ᵥ z)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        have hx0 : A *ᵥ x = 0 := hx
        have hxU : orthogonalComplementRational X u u' M₂ x := by
          refine ⟨fun a => ?_, fun b => ?_⟩
          · have := congrFun hx0 (Sum.inl a)
            rw [hA] at this
            exact this
          · have := congrFun hx0 (Sum.inr b)
            rw [hA] at this
            exact this
        obtain ⟨x₁, hx₁, hd1, hd2⟩ := hc x hxU
        have hrv : (X.B.I.P v)⁻¹ *ᵥ (X.B.I.φ v ∘ x) = rv X.B.I v x := rfl
        refine ⟨rv X.B.I v x₁, fun a => ?_, fun b => ?_, ?_, ?_⟩
        · rw [frm_one, Formalism.L2.SG.Pf.Level.hJ_rv, hx₁.1 a, map_zero]
        · rw [frm_one, Formalism.L2.SG.Pf.Level.rv_mulVec, Formalism.L2.SG.Pf.Level.hJ_rv, hx₁.2 b, map_zero]
        · rw [hrv]
          exact wCoord_eq_of_perp X u v _ _ hd1
        · rw [hrv, Formalism.L2.SG.Pf.Level.rv_mulVec, Formalism.L2.SG.Pf.Level.rv_mulVec]
          exact wCoord_eq_of_perp X u' v _ _ hd2
      | zero =>
        refine ⟨0, fun a => hJ_zero_right _ _, fun b => hJ_zero_right _ _, ?_, ?_⟩
        · rw [Matrix.mulVec_zero]
        · rw [Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.mulVec_zero]
      | add z z' _ _ hz hz' =>
        obtain ⟨y, ya, yb, yc, yd⟩ := hz
        obtain ⟨y', ya', yb', yc', yd'⟩ := hz'
        refine ⟨y + y', fun a => ?_, fun b => ?_, ?_, ?_⟩
        · rw [hJ_add_right, ya a, ya' a, add_zero]
        · rw [hJ_add_right, yb b, yb' b, add_zero]
        · rw [Matrix.mulVec_add, wCoord_add, wCoord_add, yc, yc']
        · rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, wCoord_add, wCoord_add, yd, yd']
      | smul c z _ hz =>
        obtain ⟨y, ya, yb, yc, yd⟩ := hz
        refine ⟨c • y, fun a => ?_, fun b => ?_, ?_, ?_⟩
        · rw [hJ_smul_right, ya a, mul_zero]
        · rw [hJ_smul_right, yb b, mul_zero]
        · rw [Matrix.mulVec_smul, wCoord_smul, wCoord_smul, yc]
        · rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, wCoord_smul, wCoord_smul, yd]
    have hy2 : (X.B.I.P v)⁻¹ *ᵥ (X.B.I.P v *ᵥ y₂) = y₂ := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hPu, Matrix.one_mulVec]
    obtain ⟨y₁, k1, k2, k3, k4⟩ := key _ hspan
    rw [hy2] at k3 k4
    exact ⟨y₁, k1, k2, k3, k4⟩

end Formalism.L2.SG.Pf.RowForm
