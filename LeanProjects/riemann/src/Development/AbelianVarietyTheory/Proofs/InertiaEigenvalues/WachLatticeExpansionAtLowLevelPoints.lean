import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullbackRecord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LatLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_smul (c : LL) (e : PowerSeries LL) (f : ℤ → M) : conv (c • e) f = c • conv e f := by
  funext k
  unfold conv
  simp only [Pi.smul_apply, map_smul, smul_eq_mul, mul_smul]
  rw [smul_finsum]

theorem conv_congr (e e' : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ e - e') (r : ℤ)
    (hr : r < (m : ℤ) - a) : conv e f r = conv e' f r := by
  by_cases h : r < -(a : ℤ)
  · rw [LatFil.conv_vanish e f _ hf r h, LatFil.conv_vanish e' f _ hf r h]
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, r = (q : ℤ) - a := ⟨(r + a).toNat, by omega⟩
    rw [LatFil.conv_eq_sum e f a hf, LatFil.conv_eq_sum e' f a hf]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < m := by have := Finset.mem_range.1 hj; omega
    have := (PowerSeries.X_pow_dvd_iff.1 hd) j hj'
    rw [map_sub, sub_eq_zero] at this
    rw [this]

theorem approx_step (bb c cc : LL) (e q : PowerSeries LL) (f : ℤ → M) (a m : ℕ)
    (hf : ∀ r : ℤ, r < -(a : ℤ) → f r = 0) (hd : PowerSeries.X ^ m ∣ PowerSeries.C c * q - e)
    (hcc : bb * c = cc) (r : ℤ) (hr : r < (m : ℤ) - a) : bb • conv e f r = conv (PowerSeries.C cc * q) f r := by
  subst hcc
  have h1 : bb • conv e f r = conv (PowerSeries.C bb * e) f r := by
    rw [← PowerSeries.smul_eq_C_mul, conv_smul]
    rfl
  rw [h1]
  refine conv_congr _ _ f a m hf ?_ r hr
  have h2 : PowerSeries.C bb * e - PowerSeries.C (bb * c) * q = -(PowerSeries.C bb * (PowerSeries.C c * q - e)) := by
    rw [map_mul]
    ring
  rw [h2, dvd_neg]
  exact Dvd.dvd.mul_left hd _

end Series

end GlobalTheory.NL.LatLevel

namespace GlobalTheory.NL.LatLevel

set_option maxHeartbeats 20000000 in

theorem lattice_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P4 D HW F Cm := by
  intro D HW F Cm l _ K s LL h T hT
  have hP4a := GlobalTheory.NL.LowLevel.expansions_low_and_pullback_record D HW F Cm l K s LL h T hT
  unfold p4
  refine ⟨hP4a.1, fun i ζ τ hpt => ⟨hP4a.2 i ζ τ hpt, ?_, ?_⟩⟩
  · intro x k
    have hmem : ex (Cm l) h T i ζ ((letE i : AA K LL) • x) ∈ Lat (Cm l) h T i ζ :=
      Submodule.subset_span ⟨1, _, (LowLevel.conv_one _).symm⟩
    have hk := ((LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt _).1 hmem).2 k
    rw [((Cm l).C K s LL h).tie.levN_eq]
    exact ⟨Submodule.mem_map_of_mem hk.1, hk.2⟩
  · intro k w hw
    obtain ⟨hprim, hτ, ι, hcomp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hpt
    have hC := GlobalTheory.NL.CompD.component D HW l K s LL h T hT i ζ τ ι hcomp hτ
    have hw' : w ∈ DdRE ((D.loc l).PD K) T.ρ τ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (-k) := hw
    obtain ⟨d, hd, hdw⟩ := hC.2.2.1 w (Submodule.mem_inf.1 hw').1
    have hdF : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ (-k) := by
      have e1 : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
          w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
      rw [e1]
      exact Submodule.add_mem_sup hw hdw
    have hlat := LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hpt
    have hsingle : (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) ∈ Lat (Cm l) h T i ζ := by
      refine (hlat _).2 ⟨⟨k, fun r hr => Pi.single_eq_of_ne hr.ne _⟩, fun r => ?_⟩
      by_cases hr : r = k
      · subst hr
        simp only [Pi.single_eq_same]
        exact ⟨hd, hdF⟩
      · rw [Pi.single_eq_of_ne hr, map_zero]
        exact ⟨zero_mem _, zero_mem _⟩
    have hfull := GlobalTheory.T.wach_expansions_span_full_lattice D HW F Cm l K s LL h T hT i ζ hprim
    obtain ⟨nb⟩ := @GlobalTheory.NL.N_basis D HW F l _ K s LL h T hT
    have hli := GlobalTheory.T.wachExpansion_basis_divisibility D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull
    obtain ⟨e, he⟩ := (hli.2 _ nb).2.1 _ hsingle
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, ∀ j, ∀ r : ℤ, r < -(a₀ : ℤ) → ex (Cm l) h T i ζ (nb j) r = 0 := by
      choose m hm using fun j => ((Cm l).C K s LL h).tie.levB_supp T i ζ (nb j)
      refine ⟨∑ j, (-m j).toNat, fun j r hr => hm _ _ ?_⟩
      have := Finset.single_le_sum (f := fun j => (-m j).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k < (m : ℤ) - a₀ := ⟨(k + a₀ + 1).toNat, by omega⟩
    have hwd := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.2 i ζ hprim
    choose a c hc0 hca _ using fun j => hwd (e j) m
    have t1 : ∀ j, c j • ((HW l).W K s LL h).lev i ζ (a j) =
        PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) := fun j => PowerSeries.smul_eq_C_mul _ _
    have hca' : ∀ j, PowerSeries.X ^ m ∣ PowerSeries.C (c j) * ((HW l).W K s LL h).lev i ζ (a j) - e j :=
      fun j => by rw [← t1 j]; exact hca j
    haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
      integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ↥(OL LL))
      (Finset.univ : Finset (Fin _)) c
    choose o ho using fun j => hb j (Finset.mem_univ j)
    have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) * c j = algebraMap ↥(OL LL) ↥LL.1 (o j) :=
      fun j => (Algebra.smul_def _ _).symm.trans (ho j).symm
    have hb0 : algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    let x : ↥(((HW l).W K s LL h).N T) := ∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j
    have hx : ∀ r, ex (Cm l) h T i ζ x r =
        ∑ j, conv (((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j)) (ex (Cm l) h T i ζ (nb j)) r := by
      intro r
      show ((Cm l).C K s LL h).tie.levB T i ζ (∑ j, (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) • nb j) r = _
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact congrFun (hli.1 _ _) r
    have hkey : ∀ r : ℤ, r < (m : ℤ) - a₀ →
        algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) • (Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) r =
          ex (Cm l) h T i ζ x r := by
      intro r hr
      rw [he, hx, Finset.sum_apply]
      refine Finset.smul_sum.trans (Finset.sum_congr rfl fun j _ => ?_)
      have hlev : ((HW l).W K s LL h).lev i ζ (algebraMap ↥(OL LL) (AA K LL) (o j) * a j) =
          PowerSeries.C (algebraMap ↥(OL LL) ↥LL.1 (o j)) * ((HW l).W K s LL h).lev i ζ (a j) := by
        letI : Algebra ↥(OL LL) (PowerSeries ↥LL.1) := MvPowerSeries.instAlgebra
        have hcom := (((HW l).W K s LL h).lev i ζ).commutes (o j)
        rw [map_mul, hcom, PowerSeries.algebraMap_apply]
      exact (approx_step (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL))) (c j) _ (e j)
        (((HW l).W K s LL h).lev i ζ (a j)) (ex (Cm l) h T i ζ (nb j)) a₀ m (ha₀ j) (hca' j) (ho' j) r hr).trans
        (congrArg (fun p => conv p (ex (Cm l) h T i ζ (nb j)) r) hlev.symm)
    have hl1 := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩).2.1
    have hN1 : ∀ j, ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
        ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex (Cm l) h T i ζ x j) := by
      intro j
      rw [((HW l).W K s LL h).levN_smul, hl1]
      exact (congrFun (LowLevel.conv_one (((HW l).W K s LL h).levN T i ζ x)) j).trans
        (((Cm l).C K s LL h).tie.levN_eq T i ζ x j)
    have hc : ∀ j, j ≤ k → (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹ •
        ((HW l).W K s LL h).levN T i ζ ((letE i : AA K LL) • x) j =
          ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)
            ((Pi.single k d : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B) j) := by
      intro j hj
      rw [hN1, ← map_smul, ← hkey j (by omega), inv_smul_smul₀ hb0]
    refine ⟨x, (algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)))⁻¹, inv_ne_zero hb0, fun j hj => ?_, ?_⟩
    · rw [hc j hj.le, Pi.single_eq_of_ne hj.ne, map_zero]
      exact zero_mem _
    · rw [hc k le_rfl, Pi.single_eq_same]
      exact Submodule.mem_sup_right hdw

end GlobalTheory.NL.LatLevel
