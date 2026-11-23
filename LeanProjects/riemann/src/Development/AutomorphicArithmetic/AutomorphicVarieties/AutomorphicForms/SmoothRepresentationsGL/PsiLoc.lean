import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem psiL_eq_one_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E) : psiL w x = 1 ↔ GroundTheory.Global.localAdelicChar E w x = 1 := by
  have h : psiL w x = (GroundTheory.Global.localAdelicChar E w x : ℂ) := rfl
  rw [h]
  exact Circle.coe_eq_one

private theorem exists_psiL_ne_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (z : w.adicCompletion E) (hz : z ∉ GroundTheory.Global.localInvDifferent w) :
    ∃ a ∈ w.adicCompletionIntegers E, psiL w (a * z) ≠ 1 := by
  by_contra hc
  refine hz ((GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff w z).1 fun a ha => ?_)
  rw [← psiL_eq_one_iff]
  by_contra h
  exact hc ⟨a, ha, h⟩

theorem UpperTheory.V.Af.Smo.psiLoc :
    UpperTheory.V.Af.Smo.PsiLoc := by
  intro E _ _
  refine ⟨fun w => ⟨?_, fun h => ?_⟩, ?_⟩
  · filter_upwards [(GroundTheory.Global.isOpen_localInvDifferent w).mem_nhds (zero_mem _)] with x hx
    exact (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem hx)
  · obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w
      (WithZero.exp (FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E) + 1))
    obtain ⟨a, -, ha⟩ := exists_psiL_ne_one w z (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp]
      omega)
    exact ha (by rw [h]; rfl)
  · filter_upwards [FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E)] with w hw
    refine ⟨fun x hx => (psiL_eq_one_iff w x).2 (GroundTheory.Global.localAdelicChar_eq_one_of_mem
      (GroundTheory.Global.mem_localInvDifferent_of_mem hx)), fun ϖ hϖ => ?_⟩
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h0 : ϖ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨a, haO, ha⟩ := exists_psiL_ne_one w ϖ⁻¹ (by
      rw [GroundTheory.Global.mem_localInvDifferent_iff_valued, hw, map_inv₀, hv, ← WithZero.exp_neg,
        WithZero.exp_le_exp]
      omega)
    refine ⟨a * ϖ⁻¹, ?_, ha⟩
    rw [mul_left_comm, mul_inv_cancel₀ h0, mul_one]
    exact haO
