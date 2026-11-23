import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix Filter
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

local instance rwcN {d n : ℕ} : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance rwcS {d n : ℕ} : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace

namespace RightChartMultiplication

variable {d : ℕ}

theorem vfD_contDiffOn {V : (Fin d → ℝ) → (Fin d → ℝ)} {u : (Fin d → ℝ) → ℂ} {O : Set (Fin d → ℝ)}
    (hO : IsOpen O) {m : ℕ} (hu : ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u O) (hV : ContDiffOn ℝ ∞ V O) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (vfD V u) O := by
  have h1 : ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ u x) O :=
    hu.fderiv_of_isOpen hO (by push_cast; exact le_rfl)
  exact h1.clm_apply (hV.of_le (by exact_mod_cast le_top))

theorem vfW_contDiffOn {O : Set (Fin d → ℝ)} (hO : IsOpen O) :
    ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))) (n : ℕ) (u : (Fin d → ℝ) → ℂ),
      ContDiffOn ℝ (n : WithTop ℕ∞) u O → (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) → Vs.length ≤ n →
      ContDiffOn ℝ ((n - Vs.length : ℕ) : WithTop ℕ∞) (vfW Vs u) O
  | [], n, u, hu, _, _ => by simpa [vfW] using hu
  | V :: Vs, n, u, hu, hV, hl => by
      simp only [List.length_cons] at hl
      have ih := vfW_contDiffOn hO Vs n u hu (fun W hW => hV W (List.mem_cons_of_mem _ hW)) (by omega)
      have e : n - Vs.length = (n - (Vs.length + 1)) + 1 := by omega
      rw [e] at ih
      simp only [vfW, List.length_cons]
      exact vfD_contDiffOn hO ih (hV V (List.mem_cons_self ..))

theorem glev0 {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g ∈ Q.Glev k r 0 :=
  ⟨hg, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

def mulLC {k r : ℕ} (X : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

theorem lcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
  have h1 := P.B5.curve_hasDerivAt (1 : B.Mat k r) X 0
  have h2 := (mulRightRealCLM g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [Function.comp_def, mulRightCLM_apply, Matrix.one_mul, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero] at h2
  exact h2

theorem rcurve_hasDerivAt {k r : ℕ} (X g : B.Mat k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
  have h1 := P.B5.curve_hasDerivAt g X 0
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h1
  exact h1

theorem step {k r : ℕ} {O : Set (Fin d → ℝ)} {U : Set (B.Mat k r)} {κ : (Fin d → ℝ) → B.Mat k r}
    {Φ : B.Mat k r → (Fin d → ℝ)} (hC : IsChart k r d O U κ Φ) (f : B.Mat k r → ℂ) (h : (Fin d → ℝ) → ℂ)
    (hfh : ∀ y ∈ O, f (κ y) = h y) {x : Fin d → ℝ} (hx : x ∈ O) (hh : DifferentiableAt ℝ h x)
    (c : ℝ → B.Mat k r) (v : B.Mat k r) (hc : HasDerivAt c v 0) (hc0 : c 0 = κ x)
    (hcG : ∀ t, c t ∈ B.GV k r) :
    deriv (fun t => f (c t)) 0 = fderiv ℝ h x (fderiv ℝ Φ (κ x) v) := by
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC
  have hxU : κ x ∈ U := (hκO x hx).2.1
  have hΦd : DifferentiableAt ℝ Φ (κ x) :=
    (hΦ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU.mem_nhds hxU)
  have heq : (fun t => f (c t)) =ᶠ[𝓝 0] fun t => h (Φ (c t)) := by
    filter_upwards [hmem] with t ht
    obtain ⟨h1, h2⟩ := hΦU (c t) ht (hcG t)
    rw [← hfh _ h1, h2]
  rw [heq.deriv_eq]
  have hγ : HasDerivAt (fun t => Φ (c t)) (fderiv ℝ Φ (κ x) v) 0 := by
    have := hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0.symm
    exact this
  have hγ0 : Φ (c 0) = x := by rw [hc0]; exact (hκO x hx).2.2
  exact (hh.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm).deriv

end RightChartMultiplication

open RightChartMultiplication in
theorem right_chart_holds : RwChart := by
  intro k r z z' d O U κ Φ u hC hOm hu
  have hC' := hC
  obtain ⟨hO, hU, hκ, hΦ, hκO, hΦU⟩ := hC

  have h1 : ∀ n : ℕ, n ≤ 2 * r + k + 1 → ContDiffOn ℝ (n : WithTop ℕ∞) (fun x => u (κ x)) O := by
    intro n hn x hx
    obtain ⟨V, F, hVo, hxV, hF, hFu⟩ := hu (κ x) ⟨glev0 (hκO x hx).1, hOm x hx⟩
    have hxV' : κ x ∈ V := hxV
    have hev : ∀ᶠ y in 𝓝[O] x, κ y ∈ V := (hκ.continuousOn x hx) (hVo.mem_nhds hxV')
    have hFκ : ContDiffWithinAt ℝ (n : WithTop ℕ∞) (fun y => F (κ y)) O x :=
      ((hF.contDiffAt (hVo.mem_nhds hxV')).of_le (by exact_mod_cast hn)).comp_contDiffWithinAt x
        ((hκ x hx).of_le (by exact_mod_cast le_top))
    refine hFκ.congr_of_eventuallyEq ?_ (hFu _ hxV' (glev0 (hκO x hx).1))
    filter_upwards [hev, self_mem_nhdsWithin] with y hyV hyO
    exact hFu _ hyV (glev0 (hκO y hyO).1)

  have hDΦ : ContDiffOn ℝ ∞ (fun g => fderiv ℝ Φ g) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hΦ).2
  have hDΦκ : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Φ (κ x)) O :=
    hDΦ.comp hκ (fun x hx => (hκO x hx).2.1)
  have hVR : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VR κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulRightRealCLM X).contDiff.comp_contDiffOn hκ)
  have hVL : ∀ X : B.Mat k r, ContDiffOn ℝ ∞ (VL κ Φ X) O := fun X =>
    hDΦκ.clm_apply ((mulLC X).contDiff.comp_contDiffOn hκ)
  refine ⟨h1 _ le_rfl, fun X => ⟨hVR X, hVL X⟩, ?_⟩

  have hdiff : ∀ (Vs : List ((Fin d → ℝ) → (Fin d → ℝ))), (∀ V ∈ Vs, ContDiffOn ℝ ∞ V O) →
      Vs.length + 1 ≤ 2 * r + k + 1 → ∀ x ∈ O, DifferentiableAt ℝ (vfW Vs fun y => u (κ y)) x := by
    intro Vs hVs hl x hx
    have hc := vfW_contDiffOn hO Vs (2 * r + k + 1) _ (h1 _ le_rfl) hVs (by omega)
    have hle : (1 : WithTop ℕ∞) ≤ ((2 * r + k + 1 - Vs.length : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1 - Vs.length)
    exact ((hc.differentiableOn (by
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) hle))).differentiableAt (hO.mem_nhds hx))
  intro Xs hXs hl
  induction Xs with
  | nil => intro x _; exact ⟨rfl, rfl⟩
  | cons X Xs ih =>
    have hX : B.inLie k r X := hXs X (List.mem_cons_self ..)
    have ih' := ih (fun Y hY => hXs Y (List.mem_cons_of_mem _ hY))
      (by simp only [List.length_cons] at hl; omega)
    simp only [List.length_cons] at hl
    intro x hx
    have hxG : κ x ∈ B.GV k r := (hκO x hx).1
    constructor
    · show RdV X (B.Rw Xs u) (κ x) = vfD (VR κ Φ X) (vfW (Xs.map (VR κ Φ)) fun y => u (κ y)) x
      unfold RdV vfD VR
      exact step hC' (B.Rw Xs u) _ (fun y hy => (ih' y hy).1) hx
        (hdiff _ (by simpa using fun Y _ => hVR Y) (by simpa using hl) x hx)
        (fun t : ℝ => κ x * NormedSpace.exp ((t : ℂ) • X)) (κ x * X) (rcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => P.B5.curve_mem hxG hX t)
    · show Q.LdV X (Xs.foldr Q.LdV u) (κ x) =
        vfD (VL κ Φ X) (vfW (Xs.map (VL κ Φ)) fun y => u (κ y)) x
      unfold Q.LdV vfD VL
      exact step hC' (Xs.foldr Q.LdV u) _ (fun y hy => (ih' y hy).2) hx
        (hdiff _ (by simpa using fun Y _ => hVL Y) (by simpa using hl) x hx)
        (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * κ x) (X * κ x) (lcurve_hasDerivAt X (κ x))
        (by simp [NormedSpace.exp_zero]) (fun t => Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (P.B5.exp_mem hX t) hxG)

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
