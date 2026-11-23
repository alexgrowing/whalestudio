import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
import Formalism.LocalToGlobal.Columns.RecLevelStep

noncomputable section

namespace GlobalTheory.SeeSaw.BaseFrame

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.DetSpec Matrix

theorem near_left {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hC : ∀ i j, v (C i j) ≤ 1) (hM : ∀ i j, v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : C - 1 = (C * M - 1) - C * (M - 1) := by rw [mul_sub, mul_one]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C) (N := M - 1)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_left' (hC i l)).trans_lt (hM l j)

theorem near_right {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    {C M : Matrix (Fin n) (Fin n) K} (hM : ∀ i j, v (M i j) ≤ 1) (hC : ∀ i j, v (C i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1)
    (h : ∀ i j, v ((C * M) i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1) (i j : Fin n) :
    v (M i j - (1 : Matrix (Fin n) (Fin n) K) i j) < 1 := by
  have e : M - 1 = (C * M - 1) - (C - 1) * M := by rw [_root_.sub_mul, one_mul]; abel
  have e2 := congrFun (congrFun e i) j
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_apply (M := C - 1) (N := M)] at e2
  rw [e2]
  refine Valuation.map_sub_lt _ (h i j) (Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_right' (hM l j)).trans_lt (hC i l)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem kMat_mul (P : HeightOneSpectrum (𝓞 E)) (g k : GL (Fin n) (AfE F E)) (f : Sp E n ≃ₗ[E] Sp E n) :
    kMat P (g * k) f = kMat P k 1 * kMat P g f := by
  ext1 i j
  have e : ∀ l, kMat P k 1 i l = adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 i l) := fun l => by
    show adAt F P (Col2.pullV k (Pi.single l 1) i) = _
    unfold Col2.pullV
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [Matrix.mul_apply]
  simp only [e]
  unfold kMat Col2.pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, map_sum]
  simp only [map_mul]

theorem kMat_one (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n) (i j : Fin n) :
    kMat P (1 : GL (Fin n) (AfE F E)) f i j = algebraMap E _ (f (Pi.single j 1) i) := by
  unfold kMat Col2.pullV
  rw [inv_one, Units.val_one, Matrix.one_mulVec, adAt_inclE]

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem lift_near_one {y k k' : GL (Fin n) (AfE F E)} {p p₀ : DecoF E n ST SG Q} (h : IsPtOf hc (y * k) p) (h' : IsPtOf hc (y * k') p)
    (h₀ : IsPtOf hc k' p₀) (hN : p₀.deco.1.N = stdLat E n) (w : SG) (hk : bc (prV (E := E) (w.1.under (𝓞 F))) k = 1)
    {f : Sp E n ≃ₗ[E] Sp E n} (hf : TopStep.IsLiftFr p₀.deco.1 w f) (i j : Fin n) :
    w.1.valuation E (f (Pi.single j 1) i - if i.val = j.val then 1 else 0) < 1 := by
  have hl := TopStep.liftFr_spec p.deco.2 w
  have h1 := val_kMat_sub_lt h w hl
  have h2 := val_kMat_sub_lt h' w hl
  have h3 := val_kMat_sub_lt h₀ w hf
  have e1 : kMat w.1 (y * k) (p.deco.1.liftFr w) = kMat w.1 y (p.deco.1.liftFr w) := by
    ext1 a b
    exact ZeroMove.adAt_pullV_mul w.1 y hk _ a
  rw [e1] at h1
  rw [kMat_mul] at h2
  rw [← one_mul k', kMat_mul] at h3
  have hc1 : Formalism.L2.Herm.Carries (1 : GL (Fin n) (AfE F E)) (stdLat E n) (stdLat E n) := fun x => by simp
  have i1 := val_kMat_le (P := w.1) (f := 1) (hN ▸ h₀.lat : Formalism.L2.Herm.Carries k' (stdLat E n) (stdLat E n)) fun _ => Iff.rfl
  have i2 := val_kMat_le (P := w.1) (f := f) hc1 (hN ▸ hf.1 : CharValCompare.IsFr w.1 (stdLat E n) f)
  have h4 := near_right _ i2 (near_left _ i1 h1 h2) h3 i j
  rw [kMat_one, Matrix.one_apply, if_congr (Fin.ext_iff (a := i) (b := j)) rfl rfl] at h4
  rw [← valued_algebraMap, map_sub, apply_ite (algebraMap E _), map_one, map_zero]
  exact h4

end Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SeeSaw.BaseFrame

end
