import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.HoloWirt

open Classical in
theorem clm_single_I {I : Type} (f : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    f (Pi.single i Complex.I) = Complex.I * f (Pi.single i 1) := by
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]

theorem wirt_false_eq_lineDeriv {I : Type} [Fintype I] [DecidableEq I] (i : I) (h : (I → ℂ) → ℂ) (z : I → ℂ)
    (hd : DifferentiableAt ℂ h z) : wirt i false h z = lineDeriv ℂ h z (Pi.single i 1) := by
  rw [hd.lineDeriv_eq_fderiv]
  unfold wirt
  rw [hd.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', Bool.false_eq_true, if_false]
  rw [clm_single_I]
  have e : ∀ a b : ℂ, a = b → (a + -Complex.I * (Complex.I * a)) / 2 = b := by
    rintro a b rfl
    ring_nf
    rw [Complex.I_sq]
    ring
  apply e
  congr
  exact Subsingleton.elim _ _

end GlobalTheory.HoloWirt

namespace GlobalTheory.HoloWirt

theorem iterD_holo_and_eq {I : Type} [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ)
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U) (l : List I) :
    DifferentiableOn ℂ (iterD l g) U ∧ Set.EqOn (iterD l g) (wirtWord (l.map fun i => (i, false)) g) U := by
  induction l with
  | nil => exact ⟨hg, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨hd, heq⟩ := ih
    have hat : ∀ z ∈ U, DifferentiableAt ℂ (iterD l g) z := fun z hz => hd.differentiableAt (hU.mem_nhds hz)
    have hpart : Set.EqOn (iterD (i :: l) g) (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U := by
      intro z hz
      show lineDeriv ℂ (iterD l g) z (Pi.single i 1) = _
      exact (hat z hz).lineDeriv_eq_fderiv
    refine ⟨?_, ?_⟩
    · have hf : DifferentiableOn ℂ (fun z => fderiv ℂ (iterD l g) z (Pi.single i 1)) U :=
        ((GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU hd).fderiv.differentiableOn).clm_apply
          (differentiableOn_const _)
      exact hf.congr hpart
    · intro z hz
      have hev : wirtWord (l.map fun i => (i, false)) g =ᶠ[nhds z] iterD l g :=
        Filter.eventually_of_mem (hU.mem_nhds hz) (fun y hy => (heq hy).symm)
      show partialD i (iterD l g) z = wirt i false (wirtWord (l.map fun i => (i, false)) g) z
      have hw : wirt i false (wirtWord (l.map fun i => (i, false)) g) z = wirt i false (iterD l g) z := by
        unfold wirt
        rw [hev.fderiv_eq]
      rw [hw, wirt_false_eq_lineDeriv i _ z (hat z hz)]
      rfl

theorem iterD_eq_wirtWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U,
      iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by
  intro I _ _ U g hU hg l z hz
  exact (iterD_holo_and_eq U g hU hg l).2 hz

end GlobalTheory.HoloWirt
