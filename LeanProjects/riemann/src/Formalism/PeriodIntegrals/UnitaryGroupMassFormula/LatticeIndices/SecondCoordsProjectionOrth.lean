import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.AdqHRRatV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SumKfMulZREqZero

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm MassDataIdxRed MassDataIdxSpl Matrix
  MassDataIdxFrA MassDataIdxAdA PIW.MassDataColumns
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
  (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) (Q : GL (IdxD D) (FpX X p))

abbrev adqE (a : Fin D.R.rS) : Fin X.B.I.n → TpX X p :=
  ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.eX a))

abbrev adqF (a : Fin D.R.rS) : Fin X.B.I.n → TpX X p :=
  ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.fY a))

abbrev adqZ : Fin X.B.I.n → TpX X p :=
  ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (crdOf X.B.I X.ιE X.bas (X.zu u))

theorem adq_pairR (hθ : IsSplitEquiv X p θ) (x y : Fin X.B.I.n → X.B.I.E) :
    crd2 X p θ Q (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) x) ⬝ᵥ crd1 X p θ Q (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) =
      (θ (inclR (FpX X p) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J x y))).1 := by
  rw [pair1 X p θ Q hθ, adq_hR_ratV]

theorem adq_pairM (hθ : IsSplitEquiv X p θ) (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q (adqM X hb u p *ᵥ v) ⬝ᵥ crd1 X p θ Q (adqM X hb u p *ᵥ w) =
      crd2 X p θ Q v ⬝ᵥ crd1 X p θ Q w := by
  rw [pair1 X p θ Q hθ, pair1 X p θ Q hθ, adq_hR]

theorem adq_std : (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) :=
  MassDataLevelSSteps.FrameW.frameOf_isStd X u

theorem adq_ee (u : D.what₂.Word) (hθ : IsSplitEquiv X p θ) (b a : Fin D.R.rS) :
    crd2 X p θ Q (adqE X p b) ⬝ᵥ crd1 X p θ Q (adqE X p a) = 0 := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas (X.eX b)) (crdOf X.B.I X.ιE X.bas (X.eX a)) = 0 := (adq_std X u).1 b a
  rw [adq_pairR X p θ Q hθ, h]
  simp

theorem adq_ef (u : D.what₂.Word) (hθ : IsSplitEquiv X p θ) (b a : Fin D.R.rS) :
    crd2 X p θ Q (adqE X p b) ⬝ᵥ crd1 X p θ Q (adqF X p a) = if b = a then 1 else 0 := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas (X.eX b)) (crdOf X.B.I X.ιE X.bas (X.fY a)) = if b = a then 1 else 0 := (adq_std X u).2.2.1 b a
  rw [adq_pairR X p θ Q hθ, h]
  split_ifs <;> simp

theorem adq_ez (hθ : IsSplitEquiv X p θ) (b : Fin D.R.rS) :
    crd2 X p θ Q (adqE X p b) ⬝ᵥ crd1 X p θ Q (adqZ X u p) = 0 := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas (X.eX b)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0 := (adq_std X u).2.2.2.1 b
  rw [adq_pairR X p θ Q hθ, h]
  simp

theorem adq_ze (hθ : IsSplitEquiv X p θ) (a : Fin D.R.rS) :
    crd2 X p θ Q (adqZ X u p) ⬝ᵥ crd1 X p θ Q (adqE X p a) = 0 := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0 := (adq_std X u).2.2.2.1 a
  rw [adq_pairR X p θ Q hθ, MassDataMassesW.NRatW.hE_swap X, h]
  simp

theorem adq_zf (hθ : IsSplitEquiv X p θ) (a : Fin D.R.rS) :
    crd2 X p θ Q (adqZ X u p) ⬝ᵥ crd1 X p θ Q (adqF X p a) = 0 := by
  have h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas (X.fY a)) (crdOf X.B.I X.ιE X.bas (X.zu u)) = 0 := (adq_std X u).2.2.2.2.1 a
  rw [adq_pairR X p θ Q hθ, MassDataMassesW.NRatW.hE_swap X, h]
  simp

def adqTau : FpX X p := crd2 X p θ Q (adqZ X u p) ⬝ᵥ crd1 X p θ Q (adqZ X u p)

def adqProj (y : IdxD D → FpX X p) : IdxD D → FpX X p :=
  y - ∑ a, (crd2 X p θ Q (adqE X p a) ⬝ᵥ y) • crd1 X p θ Q (adqF X p a) -
    ((adqTau X u p θ Q)⁻¹ * (crd2 X p θ Q (adqZ X u p) ⬝ᵥ y)) • crd1 X p θ Q (adqZ X u p)

theorem adq_proj_e (hθ : IsSplitEquiv X p θ) (b : Fin D.R.rS) (y : IdxD D → FpX X p) :
    crd2 X p θ Q (adqE X p b) ⬝ᵥ adqProj X u p θ Q y = 0 := by
  have hef := adq_ef X p θ Q u hθ b
  have hez := adq_ez X u p θ Q hθ b
  simp only [adqProj, dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, hef, hez, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self, sub_zero]

theorem secondCoords_projection_orth (hθ : IsSplitEquiv X p θ) (hτ : adqTau X u p θ Q ≠ 0) (y : IdxD D → FpX X p) :
    crd2 X p θ Q (adqZ X u p) ⬝ᵥ adqProj X u p θ Q y = 0 := by
  have hzf := adq_zf X u p θ Q hθ
  have ht : crd2 X p θ Q (adqZ X u p) ⬝ᵥ crd1 X p θ Q (adqZ X u p) = adqTau X u p θ Q := rfl
  simp only [adqProj, dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul, hzf, mul_zero,
    Finset.sum_const_zero, sub_zero, ht]
  field_simp
  ring

theorem adq_inG_int {z : FpX X p} (h : InG X p z) : z ∈ OvA X p := by
  obtain ⟨y, rfl⟩ := h
  exact (OvA X p).mul_mem _ _ (natCast_mem (OvA X p) _) y.2

theorem adq_dotG {a a' b b' : IdxD D → FpX X p} (ha : ∀ i, a' i ∈ OvA X p) (hb' : ∀ i, b i ∈ OvA X p)
    (hda : ∀ i, InG X p (a i - a' i)) (hdb : ∀ i, InG X p (b i - b' i)) :
    InG X p (a ⬝ᵥ b - a' ⬝ᵥ b') := by
  have key : ∀ z w : FpX X p, InG X p z → w ∈ OvA X p → InG X p (z * w) := by
    rintro z w ⟨y, rfl⟩ hw
    refine ⟨⟨(y : FpX X p) * w, (OvA X p).mul_mem _ _ y.2 hw⟩, ?_⟩
    show _ = _ * ((y : FpX X p) * w)
    ring
  have hadd : ∀ z w : FpX X p, InG X p z → InG X p w → InG X p (z + w) := by
    rintro z w ⟨y, rfl⟩ ⟨y', rfl⟩
    refine ⟨y + y', ?_⟩
    show _ = _ * ((y : FpX X p) + y')
    ring
  have hzero : InG X p 0 := ⟨0, by simp⟩
  have hsplit : a ⬝ᵥ b - a' ⬝ᵥ b' = ∑ i, (a i - a' i) * b i + ∑ i, (b i - b' i) * a' i := by
    simp only [dotProduct, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact hadd _ _ (Finset.sum_induction _ (InG X p) hadd hzero fun i _ => key _ _ (hda i) (hb' i))
    (Finset.sum_induction _ (InG X p) hadd hzero fun i _ => key _ _ (hdb i) (ha i))

theorem firstCoords_sub_adapted (v w : Fin X.B.I.n → TpX X p) :
    crd1 X p θ Q v - crd1 X p θ Q w = crd1 X p θ Q (v - w) := by
  simp only [crd1, ← Matrix.mulVec_sub]
  congr 1
  ext i
  simp [pr1, Function.comp_def]

theorem secondCoords_sub_adapted (v w : Fin X.B.I.n → TpX X p) :
    crd2 X p θ Q v - crd2 X p θ Q w = crd2 X p θ Q (v - w) := by
  simp only [crd2, ← Matrix.mulVec_sub]
  congr 2
  ext i
  simp [pr2, Function.comp_def]

theorem adq_lat_of (v w : Fin X.B.I.n → TpX X p)
    (hw : w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) (hd : v - w ∈ gLam X p) :
    v ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h := add_mem hw (Submodule.smul_le_right hd)
  simpa using h

end Loc

end MassDataIdxSteps
