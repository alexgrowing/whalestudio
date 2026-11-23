import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PhiExp
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.DvdOfDvdImage
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusUniformizerPowDvd

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section CritB

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem hasSubst_pi0_series (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries.HasSubst W.π₀₁ :=
  PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_cc hR)

def at0Hom (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : PowerSeries O →+* LetA O n :=
  Pi.ringHom fun _ => (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)).toRingHom

theorem at0Hom_apply (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f : PowerSeries O) :
    at0Hom W hR f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := by
  funext i
  show (PowerSeries.substAlgHom (hasSubst_pi0_series W hR)) f = PowerSeries.subst W.π₀₁ f
  rw [PowerSeries.coe_substAlgHom]

theorem evalZero_X_eq_pi0 (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W PowerSeries.X = W.π₀ := by
  funext i
  exact PowerSeries.subst_X (hasSubst_pi0_series W hR)

theorem evalZero_C (o : O) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.C o) = algebraMap O (LetA O n) o := by
  funext i
  simp [Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0, PowerSeries.subst_C, PowerSeries.algebraMap_eq]
  rfl

theorem evalZero_mul (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (f g : PowerSeries O) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f * g) = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g := by
  rw [← at0Hom_apply W hR, ← at0Hom_apply W hR, ← at0Hom_apply W hR, map_mul]

theorem qp_unit_EE (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπ₀ : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  obtain ⟨U, hU⟩ := hπ₀
  haveI := W.EE_complete
  have hJ : ((PD.p : ℕ) : W.EE) ∈ (⊥ : Ideal W.EE).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
      (Ideal.subset_span (Set.mem_singleton _))
  have h1 : IsUnit (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) :=
    Ideal.mem_jacobson_bot.1 hJ _
  have e : algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W) =
      (U : W.EE) * (((PD.p : ℕ) : W.EE) * ((U⁻¹ : W.EEˣ) : W.EE) + 1) := by
    rw [mul_add, mul_one, ← mul_assoc, mul_comm (U : W.EE), mul_assoc, Units.mul_inv, mul_one, hU]
    simp [Formalism.MainNotions.LiftingTheory.qp, map_add, map_natCast, add_comm]
  rw [e]
  exact U.isUnit.mul h1

theorem qp_pow_cancel (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (k : ℕ)
    {x y : W.DD T} (h : Formalism.MainNotions.LiftingTheory.qp W ^ k • x = Formalism.MainNotions.LiftingTheory.qp W ^ k • y) : x = y := by
  have hu : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k)) := by
    rw [map_pow]; exact (qp_unit_EE W hR).pow _
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) x,
    ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ k) y] at h
  exact hu.smul_left_cancel.1 h

end CritB

end Formalism.MainNotions.N.Pv.LocalLengthBound
