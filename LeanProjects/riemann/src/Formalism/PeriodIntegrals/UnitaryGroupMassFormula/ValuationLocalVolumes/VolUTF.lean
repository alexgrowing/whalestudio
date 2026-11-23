import Mathlib
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTyp

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUF

variable {D : D7} (X : HidaSetting D)

theorem star_eq (a : D.host.E) : star a = D.host.conj a := by
  apply D.host.φ₀.injective
  rw [show star a = IsCMField.complexConj D.host.E a from rfl, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply D.host.φ₀ a).symm

theorem sig_eq (b : X.B.I.E) : X.ιE (X.B.I.cm.sig b) = star (X.ιE b) := by
  have h1 : X.B.I.cm.sig b = star b := rfl
  rw [h1, X.ιE_conj, star_eq]

theorem hE_crd (x y : (VS D).V) :
    X.ιE (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas x) (crdOf X.B.I X.ιE X.bas y)) = (VS D).hT x y := by
  unfold hE Formalism.UG.hform crdOf
  simp only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe]
  simp only [sig_eq, X.J_eq, RingEquiv.apply_symm_apply]
  conv_rhs => rw [← X.bas.sum_repr x, ← X.bas.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
    RingHom.id_apply, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_eq (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    X.ιE (gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j) =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : D.host.E) else 0 := by
  unfold gramE
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, frameOf]
      rw [hE_crd, X.zu_norm]
      simp
    | cast b =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX b) (X.zu w), (X.zu_orth w b).1, map_zero]
      simp [Fin.castSucc_ne_last]
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      simp only [F0, Fin.snoc_last, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, (X.zu_orth w a).1]
      simp [Fin.castSucc_ne_last]
    | cast b =>
      simp only [F0, Fin.snoc_castSucc, frameOf]
      rw [hE_crd, X.ee]
      simp [Fin.castSucc_ne_last]

theorem gram_eq' (w : D.what₂.Word) (i j : Fin (D.R.rS + 1)) :
    gramE X.B.I.cm.sig X.B.I.J (F0 (frameOf X w)) i j =
      if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then -(((D.mem w).A.T : ℕ) : X.B.I.E) else 0 := by
  apply X.ιE.injective
  rw [gram_eq]
  split_ifs <;> simp

theorem tf_diff (u u' : D.what₂.Word) (v : PlX X) (g : ℕ) (i j : Fin (D.R.rS + 1)) :
    (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (g : Fv X.B.I.F v)⁻¹ =
      sc (E := X.B.I.E) v (if i = Fin.last D.R.rS ∧ j = Fin.last D.R.rS then
        ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) * (g : Fv X.B.I.F v)⁻¹
        else 0) := by
  unfold TFv
  simp only [Matrix.map_apply, gram_eq']
  split_ifs with h
  · rw [VolTU.sc_mul]
    congr 1
    rw [VolUTr.TrW.sc_eq, map_sub, map_natCast, map_natCast, map_neg, map_neg, map_natCast, map_natCast]
    ring
  · rw [sub_self, zero_mul, VolUTr.TrW.sc_eq, map_zero]

theorem sigR_sc (v : PlX X) (x : Fv X.B.I.F v) :
    sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v x) = sc (E := X.B.I.E) v x := by
  simp [sigR, sc, Algebra.TensorProduct.map_tmul]

end VolUF

theorem volTTFCong_of {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) :
    VolTTFCong X u u' v := by
  obtain ⟨m, hm⟩ := tCongX X u u' ⟨v, hv⟩
  have hg0 : (gAt X v : Fv X.B.I.F v) ≠ 0 := VolTU.natCast_ne_zero v (gAt_prime X v).ne_zero
  have hk : ((((D.mem u).A.T : ℕ) : Fv X.B.I.F v) - (((D.mem u').A.T : ℕ) : Fv X.B.I.F v)) *
      (gAt X v : Fv X.B.I.F v)⁻¹ = (m : Fv X.B.I.F v) := by
    have hm' : ((((D.mem u).A.T : ℕ) : ℤ) : Fv X.B.I.F v) - ((((D.mem u').A.T : ℕ) : ℤ) : Fv X.B.I.F v) =
        ((gAt X v : ℤ) : Fv X.B.I.F v) * (m : Fv X.B.I.F v) := by
      rw [← Int.cast_sub, ← Int.cast_mul]
      exact congrArg _ hm
    push_cast at hm'
    rw [hm', mul_comm, ← mul_assoc, inv_mul_cancel₀ hg0, one_mul]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only
    rw [VolUF.tf_diff, VolUF.tf_diff, VolUF.sigR_sc]
    congr 1
    simp only [and_comm]
  · simp only
    rw [VolUF.tf_diff]
    split_ifs
    · rw [hk, VolUTr.TrW.sc_eq]
      exact VolUTr.TrW.alg_mem v (_root_.intCast_mem _ m)
    · rw [VolUTr.TrW.sc_eq, map_zero]
      exact Submodule.zero_mem _

end Formalism.L2.SG.Pf.NcVal
