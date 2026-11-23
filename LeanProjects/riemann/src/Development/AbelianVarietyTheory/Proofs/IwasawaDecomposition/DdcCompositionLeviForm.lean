import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HodgeDomain.DdcChain

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.RGF ReciprocityTheory.L2DbarEstimates.Y Topology

theorem anti_eq_sum (n : ℕ) (D : V n →L[ℝ] ℂ) (c : V n) :
    (D c + Complex.I * D (Complex.I • c)) / 2 =
      ∑ k, (D (bas n k) + Complex.I * D (Complex.I • bas n k)) / 2 * (starRingEnd ℂ) (c k) := by
  rw [fc_clm_decomp n D c, fc_clm_decomp n D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  linear_combination ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * c a / 2 -
    (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem hol_eq_sum (n : ℕ) (D : V n →L[ℝ] ℂ) (c : V n) :
    (D c - Complex.I * D (Complex.I • c)) / 2 =
      ∑ k, (D (bas n k) - Complex.I * D (Complex.I • bas n k)) / 2 * c k := by
  rw [fc_clm_decomp n D c, fc_clm_decomp n D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  linear_combination (-(D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * c a / 2 +
    (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

variable {ι : Type} [Fintype ι] {p q n : ℕ}

theorem flat_unflat (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := rfl

theorem unflat_flat (z : Pt ι p q) : unflat (flat z) = z := rfl

theorem flat_I_smul (ξ : Pt ι p q) : flat (Complex.I • ξ) = Complex.I • flat ξ := rfl

def onV (e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] V n) (φ : Pt ι p q → ℂ) : V n → ℂ :=
  fun y => φ (unflat (e.symm y))

theorem dR_eq (e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] V n) (φ : Pt ι p q → ℂ) (z ζ : Pt ι p q) :
    dR φ z ζ = fderiv ℝ (onV e φ) (e (flat z)) (e (flat ζ)) := by
  let eR : (ι × Fin p × Fin q → ℂ) ≃L[ℝ] V n :=
    { e.toLinearEquiv.restrictScalars ℝ with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have h : (fun v => φ (unflat v)) = onV e φ ∘ eR := by
    funext v
    show φ (unflat v) = φ (unflat (e.symm (e v)))
    rw [e.symm_apply_apply]
  unfold dR
  rw [h, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

theorem dAnti_eq (e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] V n) (φ : Pt ι p q → ℂ) (z ζ : Pt ι p q) :
    dAnti φ z ζ = ∑ k, wdb n k (onV e φ) (e (flat z)) * (starRingEnd ℂ) (e (flat ζ) k) := by
  unfold dAnti
  rw [dR_eq e, dR_eq e, flat_I_smul, map_smul]
  exact anti_eq_sum n _ _

theorem dHol_eq (e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] V n) (φ : Pt ι p q → ℂ) (z ζ : Pt ι p q) :
    dHol φ z ζ = ∑ k, wd n k (onV e φ) (e (flat z)) * e (flat ζ) k := by
  unfold dHol
  rw [dR_eq e, dR_eq e, flat_I_smul, map_smul]
  exact hol_eq_sum n _ _

theorem ddc_eq_leviV (e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] V n) (f : Pt ι p q → ℝ) (z ξ : Pt ι p q)
    (hf : ContDiffAt ℝ 2 (onV e fun t => (f t : ℂ)) (e (flat z))) :
    ddc f z ξ = (leviV n (onV e fun t => (f t : ℂ)) (e (flat z)) (e (flat ξ)).ofLp).re / Real.pi := by
  set H := onV e fun t => (f t : ℂ) with hH
  have h1 : (fun w => dAnti (fun t => (f t : ℂ)) w ξ) =
      fun w => ∑ k, wdb n k H (e (flat w)) * (starRingEnd ℂ) (e (flat ξ) k) :=
    funext fun w => dAnti_eq e _ w ξ
  have h2 : onV e (fun w => ∑ k, wdb n k H (e (flat w)) * (starRingEnd ℂ) (e (flat ξ) k)) =
      fun y => ∑ k, wdb n k H y * (starRingEnd ℂ) (e (flat ξ) k) := by
    funext y; simp [onV, flat_unflat]
  have hd : ∀ k, DifferentiableAt ℝ (wdb n k H) (e (flat z)) := fun k => differentiableAt_wdb hf
  have h3 : ∀ j, wd n j (fun y => ∑ k, wdb n k H y * (starRingEnd ℂ) (e (flat ξ) k)) (e (flat z)) =
      ∑ k, wd n j (wdb n k H) (e (flat z)) * (starRingEnd ℂ) (e (flat ξ) k) := by
    intro j
    rw [fc_wd_sum n j Finset.univ _ _ fun k _ => (hd k).mul_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [wd]
    rw [fderiv_mul_const (hd k)]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  unfold ddc
  rw [h1, dHol_eq e, h2]
  simp only [h3, leviV, Finset.sum_mul]
  congr 2
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.HodgeDomain.DdcChain

open GlobalTheory.HodgeDomain.DdcChain in

theorem GlobalTheory.HodgeDomain.ddc_comp_holo : ∀ (ι : Type) [Fintype ι] (p q d : ℕ) (F : Pt ι p q → ReciprocityTheory.L2DbarEstimates.V d)
    (u : ReciprocityTheory.L2DbarEstimates.V d → ℝ) (z : Pt ι p q),
    (∀ᶠ v in nhds (flat z), DifferentiableAt ℂ (fun w => F (unflat w)) v) → ContDiffAt ℝ 2 u (F z) →
    ∀ ξ, ddc (u ∘ F) z ξ = (ReciprocityTheory.L2DbarEstimates.leviV d (fun v => (u v : ℂ)) (F z)
      (fderiv ℂ (fun w => F (unflat w)) (flat z) (flat ξ)).ofLp).re / Real.pi := by
  intro ι _ p q d F u z hF hu ξ
  set n := Module.finrank ℂ (ι × Fin p × Fin q → ℂ) with hn
  let e : (ι × Fin p × Fin q → ℂ) ≃L[ℂ] ReciprocityTheory.L2DbarEstimates.V n :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
  set Gf : (ι × Fin p × Fin q → ℂ) → ReciprocityTheory.L2DbarEstimates.V d := fun w => F (unflat w) with hGf
  set G : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V d := Gf ∘ e.symm with hG
  set g : ReciprocityTheory.L2DbarEstimates.V d → ℂ := fun v => (u v : ℂ) with hg
  set y0 := e (flat z) with hy0
  obtain ⟨t, ht, hto, hzt⟩ := eventually_nhds_iff.mp hF
  have hUo : IsOpen (e.symm ⁻¹' t) := hto.preimage e.symm.continuous
  have hyU : y0 ∈ e.symm ⁻¹' t := by simpa [hy0] using hzt
  have hGd : DifferentiableOn ℂ G (e.symm ⁻¹' t) := fun y hy =>
    ((ht _ hy).comp y e.symm.differentiableAt).differentiableWithinAt
  have hC : ContDiffOn ℂ 2 G (e.symm ⁻¹' t) := GlobalTheory.SCV.contDiffOn_of_differentiableOn hUo hGd 2
  have hGz : G y0 = F z := by simp [hG, hGf, hy0, unflat_flat]
  have hg2 : ContDiffAt ℝ 2 g (G y0) := by
    rw [hGz]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ hu
  have hGat : ContDiffAt ℝ 2 G y0 := ((hC y0 hyU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hH : onV e (fun t => (((u ∘ F) t : ℝ) : ℂ)) = g ∘ G := by
    funext y; rfl
  have hH2 : ContDiffAt ℝ 2 (onV e (fun t => (((u ∘ F) t : ℝ) : ℂ))) y0 := by
    rw [hH]; exact hg2.comp y0 hGat
  rw [ddc_eq_leviV e (u ∘ F) z ξ hH2, hH,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp n d g G _ hUo y0 hyU hC hg2, hGz]
  have hD : fderiv ℂ G y0 (WithLp.toLp 2 (e (flat ξ)).ofLp) = fderiv ℂ Gf (flat z) (flat ξ) := by
    rw [hG, ContinuousLinearEquiv.comp_right_fderiv]
    simp [hy0]
  simp only [hD]
