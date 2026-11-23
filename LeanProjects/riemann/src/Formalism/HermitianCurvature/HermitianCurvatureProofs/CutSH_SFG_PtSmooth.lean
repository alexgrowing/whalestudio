import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartCoefficientHasCompactSupport

open MeasureTheory
open scoped ComplexConjugate ContDiff Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PBI Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem contDiff_castM_sfg {k a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  have h1 : (fun g : B.Mat k a => D.castM rfl g) = fun g => g := by
    funext g
    simp [D.castM]
  rw [h1]
  exact contDiff_id

theorem castM_pt_sfg {k a b : ℕ} (h : a = b) (A M C : B.Mat k a) :
    (D.castM h A)⁻¹ * D.castM h M * D.castM h C = D.castM h (A⁻¹ * M * C) := by
  subst h
  simp [D.castM]

theorem contDiff_radial_embedding {k ρ m : ℕ} (e : ρ + 1 = m) : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  have hR : ContDiffAt ℝ ∞ (fun x : U.RC k 1 ρ => U.Rn k 1 ρ x) x₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => ms_rnC (f := fun y : U.RC k 1 ρ => y) contDiffAt_id i l
  unfold rn1
  exact ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).contDiffAt.comp x₀ hR

theorem point_smooth : PtSmooth := by
  intro k ρ m e
  constructor
  · have hfun : (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2) =
        fun q => D.castM e (D.castM (Nat.add_comm 1 ρ)
          ((U.Rn k 1 ρ q.2.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2 * U.Rn k 1 ρ q.2.2)) := by
      funext q
      unfold pt rn1 mc
      rw [castM_pt_sfg, castM_pt_sfg]
    rw [hfun]
    refine ((contDiff_castM_sfg e).comp (contDiff_castM_sfg (Nat.add_comm 1 ρ))).comp_contDiffOn ?_
    intro q₀ hq₀
    have ht : q₀.1.1 ≠ 0 := hq₀.1
    have hx : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_snd
    have hx' : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.2.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_snd
    have htc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.1) q₀ :=
      contDiffAt_fst.comp q₀ contDiffAt_fst
    have hZ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1) q₀ :=
      ms_ofC (f := fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => fun (_ : Fin 1) (_ : Fin 1) => q.1.1)
        (contDiffAt_pi.2 fun _ => contDiffAt_pi.2 fun _ => htc)
    have hγc : ContDiffAt ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ :=
      contDiffAt_snd.comp q₀ contDiffAt_fst
    have hμ : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => q.1.2) q₀ := fun i l =>
      contDiffAt_pi.1 (contDiffAt_pi.1 hγc i) l
    have hdet : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q₀.1.1).det ≠ 0 := by
      rw [Matrix.det_unique]; exact ht
    have hZi : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => q.1.1)ᴴ⁻¹) q₀ :=
      ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hdet)
    have hm : MS (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) =>
        U.mMap k 1 ρ (Matrix.of fun _ _ => q.1.1) q.1.2) q₀ := by
      unfold U.mMap
      exact measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
        (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)
    have hall := ms_mul (ms_mul (ms_rnC_inv hx) hm) (ms_rnC hx')
    exact (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hall i l).contDiffWithinAt
  · intro z
    have hg := contDiff_radial_embedding (k := k) e
    have hE : ∀ i l, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => rn1 e x i l) := fun i l =>
      contDiff_pi.1 (contDiff_pi.1 hg i) l
    have hell : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => ell k m z (rn1 e x)) := by
      unfold ell
      refine ContDiff.sum fun a _ => ?_
      by_cases h : a.val + 1 < m
      · simp only [dif_pos h]
        exact hE _ _
      · simp only [dif_neg h, Matrix.mulVec, dotProduct]
        exact ContDiff.sum fun b _ => (hE _ _).mul contDiff_const
    unfold psi
    have hre : ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => (((cStd * ell k m z (rn1 e x)).re : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp (contDiff_const.mul hell))
    exact Complex.contDiff_exp.comp (contDiff_const.mul hre)

end Formalism.FourierDecayAlt.P.CutSH.SFG
