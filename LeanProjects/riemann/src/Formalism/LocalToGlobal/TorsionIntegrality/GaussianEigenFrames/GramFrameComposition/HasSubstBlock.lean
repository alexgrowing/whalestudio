import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.C
open Formalism.L2.Th1.G (linSub toZ phSum tens4 inBlock)
open Formalism.G (unitBall)

namespace ToZ

variable {K : Type} [Field K]

theorem phSum_one {n : Type} [Fintype n] (ph : PowerSeries K) :
    phSum (fun _ : n => (1 : K)) ph = Formalism.L2.Th1.E.phSum ph := by
  unfold Formalism.L2.Th1.G.phSum Formalism.L2.Th1.E.phSum Formalism.InvariantFactorPaths.G7.at1
  exact Finset.sum_congr rfl fun i _ => one_smul _ _

theorem hasSubst_block {n : Type} [Finite n] (a : Fin 4) :
    MvPowerSeries.HasSubst (fun i : n => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem subst_four {n m : Type} [Finite n] {b : Fin 4 × n → MvPowerSeries m K}
    (hb : MvPowerSeries.HasSubst b) (f : MvPowerSeries n K) :
    MvPowerSeries.subst b
      (∏ a : Fin 4, MvPowerSeries.subst
        (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) f) =
      ∏ a : Fin 4, MvPowerSeries.subst (fun i => b (a, i)) f := by
  rw [← MvPowerSeries.substAlgHom_apply hb, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_comp_subst_apply (hasSubst_block a) hb]
  congr 1
  funext i
  exact MvPowerSeries.subst_X hb (a, i)

theorem cc_logForm {m : Type} [Fintype m] {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0)
    (c : m → K) :
    MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l : MvPowerSeries m K) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X j) l hl0,
      mul_zero]

theorem cc_flin {m : Type} [Fintype m] {l linv : PowerSeries K}
    (hl0 : PowerSeries.constantCoeff l = 0) (hv0 : PowerSeries.constantCoeff linv = 0) (c : m → K) :
    MvPowerSeries.constantCoeff
      (flin l linv c (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (cc_logForm hl0 c) linv hv0

theorem toZ_flin {m : Type} [Fintype m] {l linv : PowerSeries K}
    (hl0 : PowerSeries.constantCoeff l = 0) (hv0 : PowerSeries.constantCoeff linv = 0)
    (hlv : PowerSeries.subst linv l = PowerSeries.X) (c : m → K) :
    toZ linv (flin l linv c (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))) =
      PowerSeries.subst (∑ x, MvPowerSeries.C (c x) * MvPowerSeries.X x : MvPowerSeries m K) linv := by
  have e : toZ linv (∑ j, MvPowerSeries.C (c j) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l : MvPowerSeries m K) =
      ∑ x, MvPowerSeries.C (c x) * MvPowerSeries.X x := by
    rw [← Formalism.L2.Th1.G.toZHom_apply hv0, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes, Formalism.L2.Th1.G.toZHom_apply,
      Formalism.L2.Th1.G.toZ_subst_X hv0, hlv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X j))]
  rw [← e]
  exact Formalism.L2.Th1.G.mvSubst_subst (Formalism.L2.Th1.G.hasSubst_zPt hv0) (cc_logForm hl0 c) linv

theorem toZ_tensor4 {n : Type} [Fintype n] {l linv : PowerSeries K} (h : IsLogPair l linv)
    (T : MvPowerSeries n K) (γ : Matrix (Fin 4 × n) (Fin 4 × n) K) :
    toZ linv (MvPowerSeries.subst (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ)
      (Formalism.L2.Th1.E.tensor4 (MvPowerSeries.subst (fun i => Formalism.InvariantFactorPaths.G7.at1 i l) T))) =
      linSub (fun w w' => γ w w') (tens4 T) := by
  obtain ⟨hl0, -, hv0, -, hlv⟩ := h
  have hmc : MvPowerSeries.HasSubst (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => cc_flin hl0 hv0 _
  have hat : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) l hl0
  have hb : MvPowerSeries.HasSubst (fun w : Fin 4 × n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ w)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun w =>
      Formalism.L2.Th1.G.cc_toZ hv0 (cc_flin hl0 hv0 _)
  unfold Formalism.L2.Th1.G.toZ
  rw [MvPowerSeries.subst_comp_subst_apply hmc (Formalism.L2.Th1.G.hasSubst_zPt hv0)]
  change MvPowerSeries.subst (fun w : Fin 4 × n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ w)) _ = _
  unfold Formalism.L2.Th1.E.tensor4 Formalism.L2.Th1.G.linSub Formalism.L2.Th1.G.tens4 Formalism.L2.Th1.G.inBlock
  rw [subst_four hb, subst_four (Formalism.L2.Th1.G.hasSubst_lin _)]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hb' : MvPowerSeries.HasSubst (fun i : n =>
      toZ linv (Formalism.L2.Th1.E.matCoord l linv (RingHom.id K) γ (a, i))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.G.cc_toZ hv0 (cc_flin hl0 hv0 _)
  rw [MvPowerSeries.subst_comp_subst_apply hat hb']
  congr 1
  funext i
  unfold Formalism.InvariantFactorPaths.G7.at1
  rw [Formalism.L2.Th1.G.mvSubst_subst hb' (MvPowerSeries.constantCoeff_X i), MvPowerSeries.subst_X hb']
  unfold Formalism.L2.Th1.E.matCoord
  rw [toZ_flin hl0 hv0 hlv,
    ← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.L2.Th1.G.cc_linForm _)), hlv,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (Formalism.L2.Th1.G.cc_linForm _))]
  rfl

end ToZ

theorem ShapeToZ_proof : ShapeToZ := by
  intro K _ _ _ l linv ph hlp hph n _ T γ hS
  obtain ⟨κ, _, r, V, hr, hV, e⟩ := hS
  obtain ⟨e1, hInt⟩ := Formalism.L2.Th1.E.prodInt K κ (Fin 4 × n) ph r V hph hr hV
  refine ⟨Formalism.L2.Th1.E.thetaProd r V, fun d => hInt d, ?_⟩
  rw [← ToZ.toZ_tensor4 hlp, e, e1, ToZ.phSum_one]
  rfl

end Formalism.L2.Th1.GD
