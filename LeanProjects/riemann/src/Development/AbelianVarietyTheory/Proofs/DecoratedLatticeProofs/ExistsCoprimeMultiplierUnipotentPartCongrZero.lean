import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterNormMatrixInverse.FmatMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UkPart

open Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem natCast_int (c : ℕ) : (c : RA) ∈ IntAf X.B.I.F X.B.I.E := natCast_mem _ c

theorem sigA_natCast (c : ℕ) : sigA X.B.I (c : RA) = c := map_natCast _ c

theorem natsmul_Lf (c : ℕ) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : (c : RA) • y ∈ X.B.I.Lf := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem natsmul_mL (c : ℕ) {y : VA X.B.I} (hy : y ∈ mL X.B.I X.B.g) : (c : RA) • y ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy c

theorem mL_le_Lf : mL X.B.I X.B.g ≤ X.B.I.Lf := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  exact natsmul_Lf X _ hy

theorem intsmul_Lf {t : RA} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    t • y ∈ X.B.I.Lf := by
  have h := X.B.I.Lf.smul_mem (⟨t, ht⟩ : IntAf X.B.I.F X.B.I.E) hy
  rwa [Subring.smul_def] at h

theorem Z_int {t : RA} (ht : ZMod' X.B.I X.B.g t) : t ∈ IntAf X.B.I.F X.B.I.E := by
  obtain ⟨s, hs, rfl⟩ := ht; exact mul_mem (natCast_int X _) hs

theorem hA_ef (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl]
  have h := GlobalTheory.St.hform_crd_setting X (X.eX a) (X.fY b)
  rw [X.ef] at h
  have h' : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.fR b) = if a = b then 1 else 0 := by
    apply X.ιE.injective
    refine h.trans ?_; split_ifs <;> simp
  rw [h']; split_ifs <;> simp

theorem hA_fe (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if a = b then 1 else 0 := by
  rw [hA_symm X.B.I (incl X.B.I (X.eR a)), hA_ef]; split_ifs <;> simp

theorem exists_mult : ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ∀ b : Fin D.R.rS,
    (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
    (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g := by
  choose ce hce using fun b => (X.basisApprox b).1
  choose cf hcf using fun b => (X.basisApprox b).2
  refine ⟨∏ b, ce b * cf b, Nat.Coprime.prod_left fun b _ => Nat.Coprime.mul (hce b).1 (hcf b).1, fun b => ?_⟩
  have hd : ce b * cf b ∣ ∏ b, ce b * cf b := Finset.dvd_prod_of_mem _ (Finset.mem_univ b)
  obtain ⟨k, hk⟩ := hd
  rw [hk]
  constructor
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.e0 b - incl X.B.I (X.eR b)) =
        ((cf b * k : ℕ) : RA) • ((ce b : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hce b).2
  · have : ((ce b * cf b * k : ℕ) : RA) • (X.f0 b - incl X.B.I (X.fR b)) =
        ((ce b * k : ℕ) : RA) • ((cf b : RA) • (X.f0 b - incl X.B.I (X.fR b))) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this]; exact natsmul_mL X _ (hcf b).2

end GlobalTheory.UkPart

namespace GlobalTheory.UkPart
open Formalism.L2.SG.Pf.unitaryCongruence
variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem hA_sum_right (p : VA X.B.I) (v : Fin D.R.rS → VA X.B.I) :
    hA X.B.I p (∑ b, v b) = ∑ b, hA X.B.I p (v b) := by
  simpa only [hL_apply] using map_sum (hL X.B.I p) v Finset.univ

theorem core (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {p w : VA X.B.I} (hp : p ∈ X.B.I.Lf) (hw : w ∈ X.B.I.Lf)
    (ht : ∀ b, ZMod' X.B.I X.B.g (hA X.B.I (incl X.B.I (X.eR b)) ((c : RA) • w)))
    (hpe : ∀ b, ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b)))) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by
  have hf : ∀ b, (c : RA) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := fun b => by
    have e : (c : RA) • incl X.B.I (X.fR b) = (c : RA) • X.f0 b - (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [smul_sub, sub_sub_cancel]
    rw [e]; exact sub_mem (natsmul_Lf X c (X.vectorsInLattice.1 b).2) (mL_le_Lf X (hc b).2)
  set W := (c : RA) • w with hWdef
  have hW : W ∈ X.B.I.Lf := natsmul_Lf X c hw
  set t : Fin D.R.rS → RA := fun b => hA X.B.I (incl X.B.I (X.eR b)) W with htdef
  set W' := W - ∑ b, t b • incl X.B.I (X.fR b) with hW'def
  have hperp : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) W' = 0 := fun a => by
    rw [hW'def, hA_sub_right, hA_sum_right]
    simp only [hA_smul_right, hA_ef, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [htdef]; exact sub_self _
  have hv := hmN.2.2 W' hperp
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun RA).1 hv
  have hlam_eq : ∀ a, hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ W') = lam a := fun a => by
    rw [← hlam, hA_sum_right]
    simp only [hA_smul_right, hA_fe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have hcW' : (c : RA) • W' ∈ X.B.I.Lf := by
    rw [hW'def, smul_sub, Finset.smul_sum]
    refine sub_mem (natsmul_Lf X c hW) (sum_mem fun b _ => ?_)
    rw [smul_comm]; exact intsmul_Lf X (Z_int X (ht b)) (hf b)
  have hlam_int : ∀ a, (c : RA) ^ 2 * lam a ∈ IntAf X.B.I.F X.B.I.E := fun a => by
    have h := hA_int X.B.I (hf a) (K_sub_mv X.B.I hmK hcW')
    rw [Matrix.mulVec_smul, hA_smul_left, hA_smul_right, sigA_natCast, hlam_eq] at h
    rw [pow_two, mul_assoc]; exact h

  have h1 : ZMod' X.B.I X.B.g ((c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W')) := by
    rw [← hlam, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [hA_smul_right]
    have e : (c : RA) ^ 3 * (lam b * hA X.B.I p (incl X.B.I (X.eR b))) =
        ((c : RA) ^ 2 * lam b) * ((c : RA) * hA X.B.I p (incl X.B.I (X.eR b))) := by ring
    rw [e]; exact Z_smul X.B.I X.B.g (hlam_int b) (hpe b)

  have h2 : ZMod' X.B.I X.B.g ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    rw [Matrix.mulVec_sum, hA_sum_right, Finset.mul_sum]
    refine Z_sum X.B.I X.B.g _ _ fun b _ => ?_
    rw [Matrix.mulVec_smul, hA_smul_right]
    have e : (c : RA) * (t b * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (X.fR b))) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ((c : RA) • incl X.B.I (X.fR b))) * t b := by
      rw [Matrix.mulVec_smul, hA_smul_right]; ring
    rw [e]; exact Z_smul X.B.I X.B.g (hA_int X.B.I hp (K_sub_mv X.B.I hmK (hf b))) (ht b)
  have hsplit : W = W' + ∑ b, t b • incl X.B.I (X.fR b) := by rw [hW'def, sub_add_cancel]
  have e : (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
      (c : RA) ^ 3 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
      (c : RA) ^ 2 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b))) := by
    have e2 : (c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w) =
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ W') +
        hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ ∑ b, t b • incl X.B.I (X.fR b)) := by
      rw [← hA_add_right, ← Matrix.mulVec_add, ← hsplit, hWdef, Matrix.mulVec_smul, hA_smul_right]
    calc (c : RA) ^ 4 * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)
        = (c : RA) ^ 3 * ((c : RA) * hA X.B.I p ((X.B.I.fmat m - 1) *ᵥ w)) := by ring
      _ = _ := by rw [e2]; ring
  rw [e]
  exact Z_add X.B.I X.B.g h1 (Z_smul X.B.I X.B.g (pow_mem (natCast_int X c) 2) h2)

end GlobalTheory.UkPart

namespace GlobalTheory.UkPart
open Formalism.L2.SG.Pf.unitaryCongruence
variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
local notation "RA" => X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F

theorem conj_sub (x m : X.B.I.Gf) (v : VA X.B.I) :
    (X.B.I.fmat (x⁻¹ * m * x) - 1) *ᵥ v = X.B.I.fmat x⁻¹ *ᵥ ((X.B.I.fmat m - 1) *ᵥ (X.B.I.fmat x *ᵥ v)) := by
  rw [fmat_mul, fmat_mul]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← mul_assoc,
    fmat_inv_mul, one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, fmat_inv_mul, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem term (u : D.what₂.Word) (m : X.B.I.Gf) (hmK : m ∈ X.B.I.Kset) (hmN : m ∈ X.NfinU u) (c : ℕ)
    (hc : ∀ b : Fin D.R.rS, (c : RA) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g ∧
      (c : RA) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) (i j : Fin D.R.k) :
    ZMod' X.B.I X.B.g ((c : RA) ^ 4 *
      hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw j)) := by
  have hbw : X.bw j ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 j).1
  have hbwd : X.bwd i ∈ X.B.I.Lf := (X.vectorsInLattice.2.2 i).2
  have hfix : ∀ b, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR b) = incl X.B.I (X.eR b) :=
    fun b => (X.xu_fix u b).1
  rw [conj_sub, PIW.NormChiNBi.hA_left_inv X.B.I (X.xu u)⁻¹, inv_inv]
  refine core X u m hmK hmN c hc (K_mv X.B.I (X.xu_K u) hbwd) (K_mv X.B.I (X.xu_K u) hbw) (fun b => ?_) (fun b => ?_)
  ·
    rw [← hfix b, hA_smul_right, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw j) =
        (c : RA) * hA X.B.I (X.e0 b) (X.bw j) - hA X.B.I ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw j) := by
      rw [hA_smul_left, sigA_natCast, PIW.NormChiNBi.hA_sub_left]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((X.weightVectorsIntegral j).2.2 b).1)
      (PIW.NormChiNBi.hA_mL_left X.B.I X.B.g (hc b).1 hbw)
  ·
    rw [← hfix b, PIW.NormChiNBi.hA_fmat']
    have e : (c : RA) * hA X.B.I (X.bwd i) (incl X.B.I (X.eR b)) =
        (c : RA) * hA X.B.I (X.bwd i) (X.e0 b) - hA X.B.I (X.bwd i) ((c : RA) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [hA_smul_right, PIW.NormChiNBi.hA_sub_right]; ring
    rw [e]
    exact Z_sub X.B.I X.B.g (Z_smul X.B.I X.B.g (natCast_int X c) ((Formalism.L2.SG.Pf.reference_frame_congruences X).2.2.1 i b))
      (PIW.NormChiNBi.hA_mL_right X.B.I X.B.g (hc b).1 hbwd)

theorem ukPart_zmod : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf),
    m ∈ X.B.I.Kset → m ∈ X.NfinU u → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  intro D X u m hmK hmN
  obtain ⟨c, hcop, hc⟩ := exists_mult X
  refine ⟨c ^ 4, Nat.Coprime.pow_left 4 hcop, ?_⟩
  rw [Finset.mul_sum]
  refine Z_sum X.B.I X.B.g _ _ fun i _ => ?_
  split_ifs with h
  · push_cast; exact term X u m hmK hmN c hc i _
  · rw [mul_zero]; exact Z_zero X.B.I X.B.g

end GlobalTheory.UkPart
