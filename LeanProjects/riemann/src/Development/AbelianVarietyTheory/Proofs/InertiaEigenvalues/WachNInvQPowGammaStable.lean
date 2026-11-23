import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GeomSumOneAddPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamQ

theorem isUnit_one_add {O : Type} [CommRing O] (f : PowerSeries O)
    (hf : PowerSeries.constantCoeff f = 0) : IsUnit (1 + f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hf]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem gam_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  intro D HW F Cm l _ K s LL h W C u T hT k
  obtain ⟨χ, -, -, hγ₀, -, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨b, hb⟩ := ((GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s h.1).2.2.2.2.2.1 (χ W.gam)).2
  let U : AA K LL := fun _ => 1 + GlobalTheory.Cyc.XX l ↥(OL LL) s * b
  have hγQ : W.γA W.gam W.Q = W.Q * U := by
    funext i
    show W.γ₀ W.gam (W.Q i) = W.Q i * U i
    rw [hγ₀, hQ]
    exact hb
  have hUu : IsUnit U := Pi.isUnit_iff.2 fun _ => isUnit_one_add _ (by simp [GlobalTheory.Cyc.XX])
  have hγs : ∀ (a : AA K LL) (y : W.DD T), W.γ T (a • y) = W.γA W.gam a • W.γ T y := by
    intro a y
    have := W.γD_smul T W.gam (algebraMap (AA K LL) W.EE a) y
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  let v : AA K LL := ((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ)
  have hvU : v * U ^ k = 1 := by
    show (((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ) : AA K LL) * U ^ k = 1
    have e : U ^ k = ((hUu.unit ^ k : (AA K LL)ˣ) : AA K LL) := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [e, Units.inv_mul]
  have key : ∀ y : W.DD T, W.Q ^ k • W.γ T y = v • W.γ T (W.Q ^ k • y) := by
    intro y
    rw [hγs, map_pow, hγQ, mul_pow, smul_smul, mul_left_comm, hvU, mul_one]
  refine ⟨fun x hx => ?_, fun i ζ hζ => ?_⟩
  · rw [key]
    exact (W.N T).smul_mem v (W.N_Γ T W.gam _ hx)
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  have hlev := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩ hfull).1
  refine ⟨W.lev i ζ v, ?_, fun x hx hγ j => ?_⟩
  · have hg := W.gam_gen
    rw [(HW l).W_s] at hg
    have hΓ := ((Cm l).C K s LL h).tie.lev_Γ W.gam i ζ ζ s 1
      (by rw [(D.loc l).PD_p]; exact hζ) (by rw [Nat.cast_one]; exact hg.ge) (pow_one ζ).symm W.Q
    have hΓ' : W.lev i ζ W.Q * W.lev i ζ U = PowerSeries.rescale u (W.lev i ζ W.Q) := by
      rw [← map_mul, ← hγQ]; exact hΓ
    obtain ⟨w0, hw0, hQw⟩ := ((GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ).1
    rw [hQw, map_mul, PowerSeries.rescale_X] at hΓ'
    have h1 : w0 * W.lev i ζ U = PowerSeries.C u * PowerSeries.rescale u w0 := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ↥LL.1))
      linear_combination hΓ'
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul] at h2
    have hw0c : PowerSeries.constantCoeff w0 ≠ 0 := (hw0.map PowerSeries.constantCoeff).ne_zero
    have hUc : PowerSeries.constantCoeff (W.lev i ζ U) = u := by
      apply mul_left_cancel₀ hw0c
      rw [h2, mul_comm]
    have h3 := congrArg PowerSeries.constantCoeff (congrArg (W.lev i ζ) hvU)
    rw [map_mul, map_pow, map_one, map_mul, map_pow, map_one, hUc] at h3
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h3
  · have e1 : (⟨W.Q ^ k • W.γ T x, hγ⟩ : ↥(W.N T)) =
        v • (⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ : ↥(W.N T)) :=
      Subtype.ext (key x)
    have e2 : ex C h T i ζ ⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ =
        fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m :=
      funext fun m => GlobalTheory.NL.GradedLat.ex_gam C h T hT i ζ hζ.pow_eq_one ⟨W.Q ^ k • x, hx⟩ m
    rw [e1, hlev, e2]

end GlobalTheory.NL.GamQ
