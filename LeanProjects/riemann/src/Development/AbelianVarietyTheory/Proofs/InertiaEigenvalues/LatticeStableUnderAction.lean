import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LatKeep

variable {D : D7}

theorem intGL_mulVec_int {n : ℕ} (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (v : Fin n → EAf D)
    (hv : ∀ i, v i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ v) i ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => mul_mem ?_ (hv j)
  exact (y.val i j).2

theorem isFrame_mul_intGL {n : ℕ} {β : GL (Fin n) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.IsFrame (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y) Λ := by
  intro x
  rw [hβ x]
  have e1 : (((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          (((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    have hm : (β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ = Formalism.L2.DIV.intGL D.host.F D.host.E n y⁻¹ * β⁻¹ := by
      rw [_root_.mul_inv_rev, MonoidHom.map_inv]
    rw [hm, Units.val_mul, Matrix.mulVec_mulVec]
  have e2 : ((β⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x
      = ((Formalism.L2.DIV.intGL D.host.F D.host.E n y : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ
          ((((β * Formalism.L2.DIV.intGL D.host.F D.host.E n y)⁻¹ : GL (Fin n) (EAf D)) : Matrix (Fin n) (Fin n) (EAf D)) *ᵥ x) := by
    rw [e1, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  constructor
  · intro h i
    rw [e1]
    exact intGL_mulVec_int _ _ h i
  · intro h i
    rw [e2]
    exact intGL_mulVec_int _ _ h i

theorem latKeep : ∀ (D : D7) (V W : HSp D) (F : GlobalTheory.ExportSeries.Frame V W), F.Good → ∀ k ∈ GfC V,
    Formalism.UG.bc (Lev.swapAE D) (finPt V k).1 ∈ Formalism.L2.DIV.St F.βS →
    ∀ u : WO V W, u ∈ F.lat ↔ actO V W k 1 u ∈ F.lat := by
  intro D V W F hF k _ hk u
  obtain ⟨y, hy⟩ := hk
  have hfin : ((Formalism.UG.bc (Lev.swapAE D) (finPt V k).1 : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D))
      = (mt V k).map (toEAf D) := rfl
  have hβ' : Formalism.L2.DIV.IsFrame (F.βS * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) F.ΛS := isFrame_mul_intGL hF.frS y
  have hg : (F.βS * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y).val = (mt V k).map (toEAf D) * F.βS.val := by
    rw [← hfin, ← hy]
    simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, Matrix.mul_assoc]
  have hh : F.βT.val = (mt W 1).map (toEAf D) * F.βT.val := by
    have h1 : (mt W 1).map (toEAf D) = 1 := by
      rw [GlobalTheory.AdelicLatMove.mt_one]
      exact Matrix.map_one _ (toEAf D).map_zero (toEAf D).map_one
    rw [h1, Matrix.one_mul]
  constructor
  · intro hu
    exact GlobalTheory.AdelicLatMove.actO_mem_latO V W k 1 F.ΛS F.ΛS F.ΛT F.ΛT F.βS _ F.βT F.βT hF.frS hβ' hF.frT hF.frT hg hh u hu
  · intro hu
    have h2 := GlobalTheory.AdelicLatMove.actO_mem_latO V W k⁻¹ 1⁻¹ F.ΛS F.ΛS F.ΛT F.ΛT _ F.βS F.βT F.βT hβ' hF.frS hF.frT hF.frT
      (GlobalTheory.AdelicLatMove.frame_inv V k _ _ hg) (GlobalTheory.AdelicLatMove.frame_inv W 1 _ _ hh) _ hu
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W k⁻¹ 1⁻¹ u
    rw [inv_inv, inv_inv] at e
    rw [e] at h2
    exact h2

end GlobalTheory.LatKeep
