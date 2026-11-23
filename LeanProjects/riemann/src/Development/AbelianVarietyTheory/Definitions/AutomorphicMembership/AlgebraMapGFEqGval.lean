import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoordinatesFlagVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetNeZeroOfSignature
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntPair Formalism.BasicNotions
open Formalism.MainNotions.S (FlagG ZhatOM IsInCell ptMat)
open Formalism.MainNotions.S.Lat (LFlag hS Tu gS)

namespace GlobalTheory.IntTerm

section Space

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {A : Matrix (Fin S.rank) (Fin (r + 1)) E}

def colVec (S : HSpace E) {a : Type} (A : Matrix (Fin S.rank) a E) (b : a) : S.V :=
  S.frame.equivFun.symm fun i => A i b

theorem coMat_colVec {a : Type} (A : Matrix (Fin S.rank) a E) : coMat S (colVec S A) = A := by
  ext i b
  exact congrFun (S.frame.equivFun.apply_symm_apply fun i => A i b) i

theorem colVec_coMat {a : Type} (x : a → S.V) : colVec S (coMat S x) = x :=
  funext fun b => S.frame.equivFun.symm_apply_apply (x b)

def lflagOf (h : IsFrame (starRingEnd E) S.gram T A) : LFlag S r T :=
  have k (a b : Fin (r + 1)) : S.hT (colVec S A a) (colVec S A b) = TF r T a b := by
    rw [← h.2]
    conv_rhs => rw [← coMat_colVec A, pairM_coMat]
    rfl
  { fl :=
      { e := fun a => colVec S A a.castSucc
        z := colVec S A (Fin.last r)
        e_indep := by
          refine LinearIndependent.comp (v := colVec S A) ?_ _ (Fin.castSucc_injective r)
          refine LinearIndependent.map' (v := A.col) ?_ _ S.frame.equivFun.symm.ker
          obtain ⟨L, hL⟩ := h.1
          refine Matrix.mulVec_injective_iff.1 fun c d e => ?_
          simpa [Matrix.mulVec_mulVec, hL] using congrArg (L *ᵥ ·) e
        e_iso := fun a b => by rw [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
        z_orth := fun a => by rw [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
        z_norm := by rw [k]; simp [TF] }
    zt := colVec S A (Fin.last r) }

theorem frame_lflagOf (h : IsFrame (starRingEnd E) S.gram T A) : Formalism.MainNotions.S.Lat.frame (lflagOf h) = colVec S A := by
  funext a
  induction a using Fin.lastCases <;> simp [Formalism.MainNotions.S.Lat.frame, FlagG.fvec, lflagOf]

theorem coMat_lflagOf (h : IsFrame (starRingEnd E) S.gram T A) :
    coMat S (Formalism.MainNotions.S.Lat.frame (lflagOf h)) = A := by rw [frame_lflagOf, coMat_colVec]

theorem zhatL_eq (F : LFlag S r T) (F' : LFlag S r T') : Formalism.MainNotions.S.Lat.ZhatL F F' =
    pairM (starRingEnd E) S.gram (coMat S (Formalism.MainNotions.S.Lat.frame F')) (coMat S (Formalism.MainNotions.S.Lat.frame F)) := by
  ext a b
  rw [pairM_coMat]; rfl

theorem gvalL_eq (F : LFlag S r T) (F' : LFlag S r T') :
    Formalism.MainNotions.S.Lat.Gval F F' = Gq (starRingEnd E) T T' (Formalism.MainNotions.S.Lat.ZhatL F F') := by
  rw [Formalism.MainNotions.S.Lat.Gval, Formalism.MainNotions.S.Gflag, Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.leadMinorE, Formalism.MainNotions.S.leadMinorE,
    dif_pos le_rfl, dif_pos (Nat.le_succ r)]
  rfl

omit [NumberField E] [StarRing E] in

theorem liesAt_iff_isInCell (w : Formalism.MainNotions.S.Point E (r + 1)) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    LiesAt w Z ↔ IsInCell (ZhatOM Z) w := by
  have e : ZhatOM Z = Z * eps E r := by
    ext a b; simp [ZhatOM, eps, mul_comm]
  rw [e]; rfl

end Space

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u u' : D.what₂.Word}

def fixedFlag (D : D7) (u : D.what₂.Word) : LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E) :=
  lflagOf (S := hS D) (isFrame_recFrame D u)

theorem fixedFlag_e (D : D7) (u : D.what₂.Word) : (fixedFlag D u).fl.e = D.sp.hypE := funext fun a =>
  (congrFun (colVec_coMat (S := hS D) (Fin.snoc (α := fun _ => (hS D).V) D.sp.hypE (D.zmOf u))) a.castSucc).trans
    (by simp)

theorem fixedFlag_z_eq_zmOf (D : D7) (u : D.what₂.Word) : (fixedFlag D u).fl.z = D.zmOf u :=
  (congrFun (colVec_coMat (S := hS D) (Fin.snoc (α := fun _ => (hS D).V) D.sp.hypE (D.zmOf u)))
    (Fin.last _)).trans (by simp)

theorem fixedFlag_eq_lf (D : D7) (u : D.what₂.Word) : fixedFlag D u = Formalism.MainNotions.S.lf D (fixedFlag D u).fl := rfl

namespace RecTerm

variable (t : RecTerm D u u')

def abelian₂ : Submodule (𝓞 D.host.E) (hS D).V := latV (hS D) t.lat

def fl (_ : RecTerm D u u') : LFlag (hS D) D.R.rS ((Tu D u : ℕ) : D.host.E) := fixedFlag D u

def fl' : LFlag (hS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) := lflagOf (S := hS D) t.adm.1.1

theorem coMat_fl : coMat (hS D) (Formalism.MainNotions.S.Lat.frame t.fl) = recFrame D u :=
  coMat_lflagOf (isFrame_recFrame D u)

theorem coMat_fl' : coMat (hS D) (Formalism.MainNotions.S.Lat.frame t.fl') = t.fr := coMat_lflagOf _

theorem frame_fl_mem (a : Fin (D.R.rS + 1)) : Formalism.MainNotions.S.Lat.frame t.fl a ∈ t.abelian₂ :=
  t.lat_mem.2.1 (Submodule.subset_span ⟨a, 1, Iota.one_mem_dInv _, by
    rw [one_smul, ← t.coMat_fl]; rfl⟩)

theorem frame_fl'_mem (a : Fin (D.R.rS + 1)) : Formalism.MainNotions.S.Lat.frame t.fl' a ∈ t.abelian₂ :=
  t.adm.1.2.1 (Submodule.subset_span ⟨a, 1, Iota.one_mem_dInv _, by
    rw [one_smul, ← t.coMat_fl']; rfl⟩)

theorem isLift_fl : Formalism.MainNotions.S.Lat.IsLift t.abelian₂ t.fl :=
  ⟨by simpa [Formalism.MainNotions.S.Lat.frame, FlagG.fvec] using t.frame_fl_mem (Fin.last _), rfl⟩

theorem isLift_fl' : Formalism.MainNotions.S.Lat.IsLift t.abelian₂ t.fl' :=
  ⟨by simpa [Formalism.MainNotions.S.Lat.frame, FlagG.fvec] using t.frame_fl'_mem (Fin.last _), rfl⟩

theorem col_eq_of_Lam {u'' : D.what₂.Word} (t' : RecTerm D u u'') (h : t.abelian₂ = t'.abelian₂) : t.col = t'.col := by
  have e : t.lat = t'.lat := Submodule.ext (co_surjective.forall.2 fun x => by
    rw [← mem_latV, ← mem_latV]; exact SetLike.ext_iff.1 h x)
  exact (Col.existsUnique (isHermU_gram _).2 t.lat_mem).unique ⟨1, inS_one, latMap_one _⟩
    ⟨1, inS_one, (latMap_one _).trans e⟩

theorem zhatL_fl : Formalism.MainNotions.S.Lat.ZhatL t.fl t.fl' = t.Zhat := by
  rw [zhatL_eq, coMat_fl, coMat_fl']; rfl

theorem gval_fl : Formalism.MainNotions.S.Lat.Gval t.fl t.fl' = t.G := by
  rw [gvalL_eq, zhatL_fl, Term.G, normOf_eq (isFrame_recFrame D u)]; rfl

theorem algebraMap_GF_eq_gval :
    algebraMap D.host.F D.host.E (t.GF D.host.F) = Formalism.MainNotions.S.Lat.Gval t.fl t.fl' := by
  rw [gval_fl, t.algebraMap_GF]; exact (t.G_eq_minor (isFrame_recFrame D u)).symm

theorem at_iff_isInCell (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) :
    t.At w ↔ IsInCell (ZhatOM (Formalism.MainNotions.S.Lat.ZhatL t.fl t.fl')) w := by
  rw [zhatL_fl]; exact liesAt_iff_isInCell w _

theorem isInCell_ptOf (hG : t.GF D.host.F ≠ 0) (hR : t.relevant) :
    IsInCell (ZhatOM (Formalism.MainNotions.S.Lat.ZhatL t.fl t.fl')) t.ptOf :=
  (t.at_iff_isInCell _).1 (GlobalTheory.PtEx.at_ptOf_of_relevant t hR fun h => hG (t.GF_eq_zero_iff.2 h))

end RecTerm

theorem gpt_eq (T T' : ℕ) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) :
    Formalism.MainNotions.S.LocalSplitGroups.Gpt T T' w = Gq (starRingEnd D.host.E) (T : D.host.E) (T' : D.host.E) (ptMat w) := by
  rw [Formalism.MainNotions.S.LocalSplitGroups.Gpt, Formalism.MainNotions.S.LocalSplitGroups.Dmin, Formalism.MainNotions.S.LocalSplitGroups.Dmin, dif_pos le_rfl, dif_pos (Nat.le_succ _), D.conjF_eq,
    D.conjF_eq, ← bridge_star_holds D.R D.host, ← bridge_star_holds D.R D.host]
  rfl

namespace RecTerm

variable (t : RecTerm D u u')

theorem gpt_of_at {w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)} (h : t.At w) :
    Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T w = t.G :=
  (gpt_eq _ _ w).trans (h.Gq_eq (isFrame_recFrame D u))

theorem gpt_ptOf_ne_zero_iff : Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T t.ptOf ≠ 0 ↔
    t.GF D.host.F ≠ 0 ∧ t.At t.ptOf := by
  rw [gpt_eq, t.Gq_ptOf_ne_zero_iff, Ne, Ne, t.GF_eq_zero_iff]

theorem gpt_ptOf_of_not_at (h : ¬ ∃ w, t.At w) :
    Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T t.ptOf = 0 :=
  by_contra fun k => h ⟨_, (t.gpt_ptOf_ne_zero_iff.1 k).2⟩

theorem gpt_ptOf_ne_zero (hG : t.GF D.host.F ≠ 0) (hR : t.relevant) :
    Formalism.MainNotions.S.LocalSplitGroups.Gpt (D.mem u).A.T (D.mem u').A.T t.ptOf ≠ 0 :=
  t.gpt_ptOf_ne_zero_iff.2 ⟨hG, (t.at_iff_isInCell _).2 (t.isInCell_ptOf hG hR)⟩

end RecTerm

end Record

end GlobalTheory.IntTerm
