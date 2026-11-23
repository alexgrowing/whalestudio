import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesUnitOfReadInjScaleRootConjRootCoordRange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIso
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_of_indep {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (e : K →+* ℂ) (rd : V →ₛₗ[e] W)
    (hF : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun c => rd (v c))
    {μ : ℂ} {f f' : V} (hf : f ≠ 0) (h : rd f' = μ • rd f) : ∃ u : K, e u = μ := by
  have hrf : rd f ≠ 0 := (hF 1 (fun _ => f) (linearIndependent_unique_iff.2 hf)).ne_zero 0
  by_cases hli : LinearIndependent K ![f, f']
  · have h2 := hF 2 _ hli
    have h2' : LinearIndependent ℂ ![rd f, rd f'] := by
      convert h2 using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h2') (-μ) 1 (by rw [h, one_smul, neg_smul, neg_add_cancel])
    exact absurd this.2 one_ne_zero
  · rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne ((smul_eq_zero.1 hst).resolve_right hf) ht0
    have hf' : f' = (-(s / t)) • f := by
      have : t • f' = -(s • f) := eq_neg_of_add_eq_zero_right hst
      calc f' = t⁻¹ • (t • f') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    refine ⟨-(s / t), ?_⟩
    have h3 : e (-(s / t)) • rd f = μ • rd f := by rw [← h, hf', map_smulₛₗ]
    exact smul_left_injective ℂ hrf h3

theorem coordRange : CoordRange := by
  unfold CoordRange AtTw AtPts
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, fun x hx _ i p hr hm w _ j ρ hρ ν μ hν f f' hf hff => ?_⟩⟩⟩
  obtain ⟨Z⟩ := hm.2.2.series
  have hU : p.R.toRealDat.LUnif := hr.prim.unif
  have hW : p.R.toRealDat.models_HW := p.charW.base.models.HW
  have hK : (p.Sx.A ((j : ℕ) + 1)).IsKsForm := GlobalTheory.isKsForm_of_formsIso _ _ (p.nexp.fi j) (p.fw.ks j)
  exact exists_coord_of_indep _ _
    (GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ p.R p.cG p.Sx p.nexp p.v₀ ρ hρ _ j _ ν hν hU hW (Z.vec j) hK) hf hff

end GlobalTheory.BigOn.Exp
