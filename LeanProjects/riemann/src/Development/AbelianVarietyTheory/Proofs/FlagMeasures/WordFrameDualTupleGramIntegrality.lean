import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeUnimodular
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.FrameCrd

variable {D : D7} (X : HidaSetting D)

theorem sig_apply (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = starRingEnd D.host.E x := rfl

theorem vecOf_sum (x : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X x = ∑ i, x i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Module.Basis.equivFun_symm_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Equiv.sum_comp (ci X).symm]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  rw [vecOf_sum]
  simp only [crdH]
  rw [Equiv.sum_comp (ci X) (fun j => X.bas.repr y j • X.bas j)]
  exact X.bas.sum_repr y

theorem pairM_apply {α β : Type} [Fintype α] [Fintype β]
    (P : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) α D.host.E) (Q : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) β D.host.E)
    (a : α) (b : β) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) Q P a b =
      (VS D).hT (vecOf X fun i => P i a) (vecOf X fun i => Q i b) := by
  rw [vecOf_sum, vecOf_sum]
  simp only [GlobalTheory.SgAlg.pairM, GlobalTheory.SgAlg.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Jc,
    map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, sig_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RingHom.id_apply]
  ring

theorem col_last (u : D.what₂.Word) : (fun i => Pc X u i (Fin.last D.R.rS)) = crdH X (X.zu u) := by
  funext i; simp [Pc]

theorem col_cs (u : D.what₂.Word) (a : Fin D.R.rS) : (fun i => Pc X u i a.castSucc) = crdH X (X.eX a) := by
  funext i; simp [Pc]

theorem col_f (a : Fin D.R.rS) : (fun i => fc X i a) = crdH X (X.fY a) := by
  funext i; simp [fc]

theorem hT_swap_zero {x y : (VS D).V} (h : (VS D).hT x y = 0) : (VS D).hT y x = 0 := by
  rw [← (VS D).herm.eq x y, h, map_zero]

theorem T_ne_zero (u : D.what₂.Word) : ((((D.mem u).A.T : ℕ) : D.host.E)) ≠ 0 :=
  Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero

theorem gram_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (Pc X u) =
      GlobalTheory.SgAlg.TF D.R.rS (algebraMap D.host.F D.host.E (Tc u)) := by
  ext a b
  rw [pairM_apply]
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [col_last, vecOf_crdH, X.zu_norm]; simp [GlobalTheory.SgAlg.TF, Tc]
    | cast b =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [GlobalTheory.SgAlg.TF, (Fin.castSucc_ne_last b).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [col_last, col_cs, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).1]
      simp [GlobalTheory.SgAlg.TF, Fin.castSucc_ne_last a]
    | cast b =>
      rw [col_cs, col_cs, vecOf_crdH, vecOf_crdH, X.ee]
      simp [GlobalTheory.SgAlg.TF, Matrix.diagonal_apply, Fin.castSucc_ne_last a]

theorem free_frame (u : D.what₂.Word) : GlobalTheory.SgAlg.Free (Pc X u) := by
  have hT0 := T_ne_zero u
  let Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.of fun i c => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.fY a) i) c
  let Dg : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    Matrix.diagonal fun c => Fin.lastCases (-(((D.mem u).A.T : ℕ) : D.host.E))⁻¹ (fun _ => 1) c
  refine ⟨Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X), ?_⟩
  have h : Dg * (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * Jc X) * Pc X u =
      Dg * GlobalTheory.SgAlg.pairM (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) Y := by
    simp only [GlobalTheory.SgAlg.pairM, Matrix.mul_assoc]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, pairM_apply]
  induction c using Fin.lastCases with
  | last =>
    have hy : (fun i => Y i (Fin.last D.R.rS)) = crdH X (X.zu u) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last => rw [hy, col_last, vecOf_crdH, X.zu_norm]; simp [hT0]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, hT_swap_zero (X.zu_orth u b).1]
      simp [(Fin.castSucc_ne_last b).symm]
  | cast a =>
    have hy : (fun i => Y i a.castSucc) = crdH X (X.fY a) := by funext i; simp [Y]
    induction d using Fin.lastCases with
    | last =>
      rw [hy, col_last, vecOf_crdH, vecOf_crdH, (X.zu_orth u a).2]
      simp [Fin.castSucc_ne_last a]
    | cast b =>
      rw [hy, col_cs, vecOf_crdH, vecOf_crdH, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
      by_cases hab : a = b
      · subst hab; simp
      · simp [hab, Ne.symm hab]

theorem dual_frame (u : D.what₂.Word) :
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) := by
  refine ⟨?_, ?_⟩
  · ext a b
    rw [pairM_apply, col_f, vecOf_crdH]
    induction a using Fin.lastCases with
    | last =>
      rw [col_last, vecOf_crdH, hT_swap_zero (X.zu_orth u b).2]
      simp [(Fin.castSucc_ne_last b).symm]
    | cast a =>
      rw [col_cs, vecOf_crdH, X.ef]
      simp
  · ext a b
    rw [pairM_apply, col_f, col_f, vecOf_crdH, vecOf_crdH, X.ff]
    simp

theorem aaD_eq (a : Fin D.R.rS) : aaD D a = GlobalTheory.SgGlob.dInv D.host.E (D.R.rS - a) := by
  rw [aaD, GlobalTheory.IntTerm.Conv.ddS_eq, GlobalTheory.SgGlob.dInv, ← Nat.cast_sub a.2.le, _root_.zpow_neg, _root_.zpow_natCast,
    inv_pow]

theorem tupLat_le (u : D.what₂.Word) :
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  rw [GlobalTheory.SnMass.tupLat, Submodule.span_le]
  rintro _ ⟨b, x, hx, rfl⟩
  show vecOf X (x • fun i => GlobalTheory.SnMass.sideM (Pc X u) (fc X) i b) ∈ (VS D).L0
  rw [LinearMap.map_smul, X.Lam_split]
  induction b using Fin.addCases with
  | left c =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_left]
    simp only [GlobalTheory.SnMass.id1, Fin.append_left] at hx
    induction c using Fin.lastCases with
    | last =>
      simp only [Fin.val_last, Nat.sub_self, GlobalTheory.SgGlob.dInv, pow_zero] at hx
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [col_last, vecOf_crdH, algebraMap_smul]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (X.Lb.smul_mem o (X.zu_Lb u)))
    | cast a =>
      simp only [Fin.val_castSucc] at hx
      rw [← aaD_eq] at hx
      rw [col_cs, vecOf_crdH]
      exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, x, hx, rfl⟩))
  | right a =>
    simp only [GlobalTheory.SnMass.sideM, Fin.append_right]
    simp only [GlobalTheory.SnMass.id1, Fin.append_right] at hx
    rw [← aaD_eq] at hx
    rw [col_f, vecOf_crdH]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, x, hx, rfl⟩)

end GlobalTheory.CovDom.FrameCrd

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.FrameCrd in

theorem frame_dual_lat : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word),
    GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧
    GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧
    GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X :=
  fun _ X u => ⟨⟨free_frame X u, gram_frame X u⟩, dual_frame X u, tupLat_le X u⟩

end GlobalTheory.CovDom
