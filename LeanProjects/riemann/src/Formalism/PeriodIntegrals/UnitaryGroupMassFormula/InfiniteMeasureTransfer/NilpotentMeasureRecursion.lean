import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.ConjSubMulVec

noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge Formalism.L2.SG.HidaSetting
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso I)

abbrev Mv (g : HI I) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ := (hmI I g).map (thI I v)

theorem uMat_toInf (s : I.Ginf) (v : InfinitePlace I.F) :
    uMat (s v) = (I.P v)⁻¹ * Mv I (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) v * I.P v := by
  have h := congrFun (betaI_toInfL I hb s) v
  rw [← h]
  exact betaV_val I v _

theorem lin_eq (g : HI I) (w : Fin I.n → TI I) :
    Formalism.L2.SG.Sub.lin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g w = hmI I g *ᵥ w := rfl

theorem thV_lin_sub (g : HI I) (v : InfinitePlace I.F) (w : Fin I.n → TI I) :
    thV I v (Formalism.L2.SG.Sub.lin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g w - w) =
      (Mv I g v - 1) *ᵥ thV I v w := by
  rw [lin_eq, thV_sub, thV_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem rv_eq (v : InfinitePlace I.F) (x : Fin I.n → I.E) : rv I v x = (I.P v)⁻¹ *ᵥ phV I v x := rfl

theorem Pinv_mulVec_P_mulVec (v : InfinitePlace I.F) (y : Fin I.n → ℂ) : (I.P v)⁻¹ *ᵥ (I.P v *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)), Matrix.one_mulVec]

theorem conj_mem_iff {m : ℕ} (g : HI I) (v : InfinitePlace I.F) (Y : Fin m → Fin I.n → I.E) (t : Set (Fin m))
    (u : Fin I.n → ℂ) :
    ((I.P v)⁻¹ * Mv I g v * I.P v - 1) *ᵥ ((I.P v)⁻¹ *ᵥ u) ∈
        Submodule.span ℂ ((fun a => (I.P v)⁻¹ *ᵥ phV I v (Y a)) '' t) ↔
      (Mv I g v - 1) *ᵥ u ∈ Submodule.span ℂ ((fun a => phV I v (Y a)) '' t) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
  have hPi : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hL : ((I.P v)⁻¹ * Mv I g v * I.P v - 1) *ᵥ ((I.P v)⁻¹ *ᵥ u) =
      (I.P v)⁻¹ *ᵥ ((Mv I g v - 1) *ᵥ u) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
  have himg : (fun a => (I.P v)⁻¹ *ᵥ phV I v (Y a)) '' t =
      (Matrix.mulVecLin (I.P v)⁻¹) '' ((fun a => phV I v (Y a)) '' t) := by
    rw [Set.image_image]
    rfl
  rw [hL, himg, Submodule.span_image]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h2 := congrArg (fun x => I.P v *ᵥ x) hxy
    simp only [Matrix.mulVecLin_apply, hPi] at h2
    rw [← h2]
    exact hy
  · intro h
    exact ⟨_, h, rfl⟩

theorem fix_iff (g : HI I) (x : Fin I.n → I.E) :
    Formalism.L2.SG.Sub.lin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g
              (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) =
              Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x ↔
      ∀ v, ((I.P v)⁻¹ * Mv I g v * I.P v) *ᵥ rv I v x = rv I v x := by
  have key : ∀ v, ((I.P v)⁻¹ * Mv I g v * I.P v) *ᵥ rv I v x = rv I v x ↔
      Mv I g v *ᵥ phV I v x = phV I v x := by
    intro v
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have hPi : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [rv_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPi]
    constructor
    · intro h
      have h2 := congrArg (fun y => I.P v *ᵥ y) h
      simpa only [hPi] using h2
    · intro h
      rw [h]
  constructor
  · intro h v
    rw [key]
    have h2 := congrArg (thV I v) h
    rw [lin_eq, thV_mulVec, thV_ratV] at h2
    exact h2
  · intro h
    apply thV_ext (I := I)
    intro v
    rw [lin_eq, thV_mulVec, thV_ratV]
    exact (key v).1 (h v)

theorem tup_all {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (Q : (Fin I.n → I.E) → Prop) :
    (∀ b, Q (Formalism.L2.SG.Sub.tupH (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) b)) ↔
      ∀ x ∈ Set.range e ∪ Set.range f ∪ {z}, Q x := by
  simp only [Formalism.L2.SG.Sub.tupH, Formalism.L2.SG.Sub.F0]
  constructor
  · intro h x hx
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · have h2 := h (Fin.castAdd r (Fin.castSucc a))
      rwa [Fin.append_left, Fin.snoc_castSucc] at h2
    · have h2 := h (Fin.natAdd (r + 1) a)
      rwa [Fin.append_right] at h2
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h2 := h (Fin.castAdd r (Fin.last r))
      rwa [Fin.append_left, Fin.snoc_last] at h2
  · intro h b
    induction b using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last]
        exact h _ (by simp)
      | cast a =>
        rw [Fin.snoc_castSucc]
        exact h _ (by simp)
    | right j =>
      rw [Fin.append_right]
      exact h _ (by simp)

theorem hermitian_measure_recursion : HStep := by
  intro I hb r e f z s
  have hmem : ∀ g : HI I, g ∈ Formalism.L2.SG.Sub.Hsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
      (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) ↔
      ∀ b, Formalism.L2.SG.Sub.lin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J g (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
          (Formalism.L2.SG.Sub.tupH (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) b)) =
        Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
          (Formalism.L2.SG.Sub.tupH (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) b) := by
    intro g
    simp only [Formalism.L2.SG.Sub.Hsub, Formalism.L2.SG.Sub.stabT, MulAction.mem_stabilizer_iff]
    exact funext_iff
  refine (hmem _).trans ((tup_all I e f z (fun x => Formalism.L2.SG.Sub.lin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
    (Formalism.L2.SG.Pf.MeasInf.toInfL I hb s) (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) =
      Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x)).trans ?_)
  simp only [Formalism.L2.SG.HidaSetting.Hset, Set.mem_setOf_eq]
  constructor
  · intro h v x hx
    rw [uMat_toInf I hb s v]
    exact (fix_iff I _ x).1 (h x hx) v
  · intro h x hx
    exact (fix_iff I _ x).2 fun v => by
      rw [← uMat_toInf I hb s v]
      exact h v x hx

theorem span_lt_eq {m : ℕ} (b : Fin m) : {a : Fin m | a < b} = {c : Fin m | c.1 < b.1} :=
  Set.ext fun _ => Fin.lt_iff_val_lt_val

theorem span_univ_eq (m : ℕ) : (Set.univ : Set (Fin m)) = {c : Fin m | c.1 < m} :=
  Set.ext fun c => ⟨fun _ => c.2, fun _ => Set.mem_univ _⟩

def Acond {r : ℕ} (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) ℂ)
    (v : InfinitePlace I.F) : Prop :=
  (∀ a : Fin r, (M - 1) *ᵥ phV I v (e a) ∈
      Submodule.span ℂ ((fun c => phV I v (e c)) '' {c | c.1 < a.1})) ∧
    (M - 1) *ᵥ phV I v z ∈ Submodule.span ℂ ((fun c => phV I v (e c)) '' {c | c.1 < r}) ∧
    ∀ u, (∀ a, Bv I v (phV I v (e a)) u = 0) →
      (M - 1) *ᵥ u ∈ Submodule.span ℂ ((fun c => phV I v (e c)) '' {c | c.1 < r})

theorem inN_iff {r : ℕ} (g : HI I) (v : InfinitePlace I.F) (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) :
    InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) ((I.P v)⁻¹ * Mv I g v * I.P v) ↔
      Acond I e z (Mv I g v) v := by
  simp only [Formalism.L2.SG.HidaSetting.InN, Formalism.L2.SG.HidaSetting.InS, Formalism.L2.SG.HidaSetting.spanLt, Acond, rv_eq]
  rw [and_assoc]
  refine and_congr (forall_congr' fun a => conj_mem_iff I g v e _ _)
    (and_congr (conj_mem_iff I g v e _ _) ?_)
  constructor
  · intro h u hu
    have h2 := h ((I.P v)⁻¹ *ᵥ u) (fun a => by rw [hJ_conj]; exact hu a)
    exact (conj_mem_iff I g v e _ u).1 h2
  · intro h y hy
    have hy' : y = (I.P v)⁻¹ *ᵥ (I.P v *ᵥ y) := (Pinv_mulVec_P_mulVec I v y).symm
    rw [hy'] at hy ⊢
    exact (conj_mem_iff I g v e _ _).2 (h _ fun a => by rw [← hJ_conj]; exact hy a)

theorem nsub_iff {r : ℕ} (g : HI I) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) (T : I.F)
    (hstd : (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r).IsStd I.cm.sig I.J T) :
    g ∈ Formalism.L2.SG.Sub.Nsub (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
        (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) ↔ ∀ v, Acond I e z (Mv I g v) v := by
  have hz : ∀ a, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE I.cm.sig I.J (e a) z = 0 := hstd.2.2.2.1
  constructor
  · intro hg v
    obtain ⟨h1, h2⟩ := hg
    refine ⟨fun a => ?_, ?_, fun u hu => ?_⟩
    · have h3 := (mem_spanR_iff (I := I) e _ _).1 (h1 a) v
      rw [thV_lin_sub, thV_ratV] at h3
      exact h3
    · have hw : Formalism.L2.SG.Sub.InXperp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) z) := by
        intro a
        apply thI_inj (I := I)
        intro v'
        rw [thI_hR, thV_ratV]
        exact (phi_hE (I := I) v' (e a) z).symm.trans (by rw [hz a, map_zero])
      have h3 := (mem_spanR_iff (I := I) e _ _).1 (h2 _ hw) v
      rw [thV_lin_sub, thV_ratV, span_univ_eq] at h3
      exact h3
    · obtain ⟨w, hw⟩ := exists_single (I := I) v u
      have hx : Formalism.L2.SG.Sub.InXperp (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig I.J
          (⟨e, f, z⟩ : Formalism.L2.SG.Sub.Frame I.E I.n r) w := by
        intro a
        apply thI_inj (I := I)
        intro v'
        rw [thI_hR, hw v']
        split_ifs with hv
        · subst hv
          exact hu a
        · simp [Bv]
      have h3 := (mem_spanR_iff (I := I) e _ _).1 (h2 _ hx) v
      rw [thV_lin_sub, hw v, if_pos rfl, span_univ_eq] at h3
      exact h3
  · intro h
    refine (show _ ∧ _ from ⟨fun b => ?_, fun w hw => ?_⟩)
    · rw [mem_spanR_iff (I := I)]
      intro v
      rw [thV_lin_sub, thV_ratV]
      exact (h v).1 b
    · rw [mem_spanR_iff (I := I)]
      intro v
      rw [thV_lin_sub, span_univ_eq]
      refine (h v).2.2 _ fun a => ?_
      rw [← thI_hR]
      exact (congrArg (thI I v) (hw a)).trans (map_zero _)

theorem nilpotent_measure_recursion : NStep := by
  intro I hb r e f z T hstd s
  rw [nsub_iff I _ e f z T hstd]
  simp only [Formalism.L2.SG.HidaSetting.Ninf, Set.mem_setOf_eq]
  refine forall_congr' fun v => ?_
  rw [uMat_toInf I hb s v, inN_iff]

end Formalism.L2.SG.Pf.MeasInfW
