import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bridge
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

def brN (D : D7) : ℝ :=
  ((FractionalIdeal.absNorm (D.host.AA0 *
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ)

theorem discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by
  have := D.host.hyp.2.2.2.1
  omega

theorem br_sqrt_mem (D : D7) : D.host.sqrtMinusD ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ D.host.sqd

theorem br_sqrtE_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  exact D.host.sqd_sq

theorem br_sqrt_sq (D : D7) :
    (⟨D.host.sqrtMinusD, br_sqrt_mem D⟩ : D.host.K) ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact br_sqrtE_sq D

theorem br_finrank_K (D : D7) : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) D.host.hyp.2.1.pos D.host.sqd_sq

theorem br_finrank_E (D : D7) :
    Module.finrank ℚ D.host.E = 2 * Module.finrank D.host.K D.host.E := by
  rw [← Module.finrank_mul_finrank ℚ D.host.K D.host.E, br_finrank_K]

theorem br_emb_injective (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have hx : ∀ x, D.host.sigmaOf g x = D.host.sigmaOf g' x := fun x =>
    D.host.φ₀.injective (by simpa [Formalism.BasicNotions.Host.emb] using RingHom.congr_fun h x)
  exact D.host.gal.symm.injective (AlgEquiv.ext hx)

theorem br_embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext (br_emb_injective D h))

theorem br_sigma_fix (D : D7) (g : D.R.GG) (hg : g ∈ D.R.Psi) (y : D.host.K) :
    D.host.sigmaOf g (algebraMap D.host.K D.host.E y) = algebraMap D.host.K D.host.E y := by
  have hfix : D.host.sigmaOf g D.host.sqd = D.host.sqd := by
    have h1 := (D.host.toHostAx.galE_mem_Psi_iff (D.host.sigmaOf g)).mp
    apply h1
    simpa [Formalism.BasicNotions.Host.sigmaOf] using hg
  have hext : ((D.host.sigmaOf g : D.host.E ≃ₐ[ℚ] D.host.E) : D.host.E →ₐ[ℚ] D.host.E).comp D.host.K.val =
      D.host.K.val := by
    refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := D.host.K) (s := {D.host.sqd}) rfl ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simpa using hfix
  exact congrArg (fun φ => φ y) hext

theorem br_embT_res (D : D7) (τ : D.what₂.Tau) (y : D.host.K) :
    embT D τ (algebraMap D.host.K D.host.E y) = brPhi D y := by
  show D.host.emb (D.eTau τ : D.R.GG) (algebraMap D.host.K D.host.E y) = brPhi D y
  simp only [Formalism.BasicNotions.Host.emb, brPhi, RingHom.comp_apply, RingHom.coe_coe]
  rw [br_sigma_fix D _ (D.eTau τ).2 y]

theorem br_card_tau (D : D7) : Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E := by
  rw [D.what₂.card_Tau]
  have h1 := br_finrank_E D
  have h2 := D.host.toHostAx.finrank_cmField
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  omega

theorem leading_constant_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  intro h
  simp only [Formalism.BasicNotions.Host.AA0, inv_eq_zero, FractionalIdeal.coeIdeal_eq_zero] at h
  have h2 := D.host.𝔟_spec.1
  rw [h, Submodule.bot_mul] at h2
  exact differentIdeal_ne_bot h2

theorem br_b_spec (D : D7) :
    differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = D.host.𝔟 * (D.host.conj • D.host.𝔟) := D.host.𝔟_spec.1

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
