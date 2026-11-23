import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DvdOfOhat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslMul

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private noncomputable def dnR : GA ℚ 2 →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map ev).comp (Matrix.GeneralLinearGroup.map (TR.pInf ℚ))

private theorem dnR_upR (h : GL (Fin 2) ℝ) : dnR (upR h) = h := by
  show Matrix.GeneralLinearGroup.map ev (Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (TR.infGL ℚ 2 _)) = h
  rw [TR.pInf_infGL]
  exact Units.ext (Matrix.ext fun i j => rfl)

private theorem dnR_finGL (u : GL (Fin 2) (Af ℚ)) : dnR (finGL ℚ 2 u) = 1 := by
  show Matrix.GeneralLinearGroup.map ev (Matrix.GeneralLinearGroup.map (TR.pInf ℚ) (finGL ℚ 2 u)) = 1
  rw [TR.pInf_finGL, map_one]

private theorem pFin_upR (h : GL (Fin 2) ℝ) : Matrix.GeneralLinearGroup.map (pFin ℚ) (upR h) = 1 :=
  TR.pFin_infGL _

private theorem comp_eq {γ γ' : GL (Fin 2) ℚ} {h h' : GL (Fin 2) ℝ} {u u' : GL (Fin 2) (Af ℚ)}
    (e : ratGL ℚ 2 γ * (upR h * finGL ℚ 2 u) = ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u')) :
    h' = toR (γ'⁻¹ * γ) * h ∧ toF (γ'⁻¹ * γ) = u' * u⁻¹ := by
  rw [ratGL_eq, ratGL_eq] at e
  have e1 := congrArg dnR e
  have e2 := congrArg (Matrix.GeneralLinearGroup.map (pFin ℚ)) e
  simp only [map_mul, dnR_upR, dnR_finGL, mul_one] at e1
  simp only [map_mul, pFin_upR, pFin_finGL, one_mul] at e2
  constructor
  · rw [map_mul, map_inv, mul_assoc, e1, inv_mul_cancel_left]
  · rw [map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc, e2, inv_mul_cancel_left]

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.liftEx :
    UpperTheory.V.Af.Nf.LiftEx := by
  intro k M hM f hf
  choose γ h u hu e using decomp M hM
  refine ⟨fun g => nsl k f (h g) UpperHalfPlane.I, fun γ' h' u' hu' => ?_⟩
  obtain ⟨e1, e2⟩ := comp_eq (e (ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u')))
  have hK := (K1G M).mul_mem (hu (ratGL ℚ 2 γ' * (upR h' * finGL ℚ 2 u'))) ((K1G M).inv_mem hu')
  rw [← e2] at hK
  obtain ⟨δ, hδ, hc⟩ := (ratK M hM).1 _ hK
  have hd : h'.val.det ≠ 0 := (Matrix.isUnits_det_units h').ne_zero
  have hi := (nslInv k M f h'.val hd).1 hf δ hδ
  show nsl k f (h _).val UpperHalfPlane.I = _
  rw [e1, Units.val_mul]
  rcases hc with hc | hc
  · rw [hc, hi]
  · rw [hc, mul_assoc, (nslMul k f).2.1, hi]
