import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionPointsIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IpNormPowSubPowLe
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Pair

namespace BiextensionSums

theorem simeq_sum {K ι α : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    (s : Finset α) (f g : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Simeq (f a) (g a)) :
    Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem subst_sumE {K ι κ : Type} [Field K] [Fintype ι] {N0 N1 : ℕ}
    {Xt : Bool × ι × Fin N0 × Fin N1 → MvPowerSeries κ K}
    (h0 : ∀ x, constantCoeff (Xt x) = 0) (be : MvPowerSeries (Fin 2) K) :
    subst Xt (sumE be) = ∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be := by
  have hX : HasSubst Xt := hasSubst_of_constantCoeff_zero h0
  unfold sumE
  rw [subst_sum hX]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (by intro a; simp)) hX]
  congr 1
  funext a
  rw [subst_X hX]
  fin_cases a <;> rfl

end BiextensionSums

open BiextensionSums

theorem biextension_points_of_exp_spec (hE : ExpSpec) (hM : MeanSimeqL) : BiextensionPointsIntegral := by
  intro K _ _ _ l d N0 N1 _ σ hU h2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hTr ζ hζ
  have hl : 2 ≤ l := hU.1.two_le
  have hLS := fun a b => (letter_shift K l d σ hU.1).2.2 N0 N1 a b
  have hSI := ShiftIP_of_frobSq frobenius_square K l d σ hU hd (Formalism.DworkPowerSeriesWeights.ZV d N0 N1)
  have hIP : ∀ x : Bool × ι × Fin N0 × Fin N1, IP l σ
      (if x.1 = false then
        linEL (d := d) σ (oms x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))
      else linOL (d := d) σ (om x.2.1) (fun s => entLog (K := K) l (s, x.2.2.1, x.2.2.2))) := by
    intro x
    split_ifs
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (oms x.2.1) (hOw.1 x.2.1).2 (hOw.2 x.2.1).2).1
    · exact (hSI _ (hLS x.2.2.1 x.2.2.2) (om x.2.1) (hOw.1 x.2.1).1 (hOw.2 x.2.1).1).2
  choose Xt h0 hi hlog using fun x => integral_part_lemma K l σ hU _ _ (hIP x)
  refine ⟨Xt, fun x => ⟨h0 x, hi x⟩, hlog, ?_⟩
  have hsum : (∑ e : ι × Fin N0 × Fin N1, subst ![Xt (false, e), Xt (true, e)] be0) =
      ∑ ab : Fin N0 × Fin N1, ∑ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [subst_sumE h0, hsum]
  refine simeq_sum (K := K) _ _ _ fun ab _ => ?_
  have key := hM K l d σ hU h2 hd F hF be0 hF1 hF2 ι om oms hOw hTr ζ hζ _
    (fun s => entLog (K := K) l (s, ab.1, ab.2)) (hLS ab.1 ab.2)
  rw [subst_tilde K l d σ hl be0 ι om oms _ _ (fun s => (hLS ab.1 ab.2 s).1)] at key
  have e : ∀ r : ι, subst ![Xt (false, r, ab), Xt (true, r, ab)] be0 =
      subst ![linEL (d := d) σ (oms r) (fun s => entLog (K := K) l (s, ab.1, ab.2)),
        linOL (d := d) σ (om r) (fun s => entLog (K := K) l (s, ab.1, ab.2))] (addC l be0) := by
    intro r
    rw [← addC_log hE hl (h0 _) (h0 _), hlog, hlog]
    simp
  simp only [e]
  exact key

end Formalism.L2.Th1.D
