import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.OfVecFixedIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep
open UpperTheory.Gal.CharacterCongruences

theorem UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds :
    UpperTheory.Gal.CharacterCongruences.NeatOfPlace := by
  intro E _ _ _ a C hC u hT g γ hγ c hc x hx h
  have hxl : cLoc u x = 1 := by
    have h0 : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h1 : cLoc u x = Matrix.GeneralLinearGroup.map (pLoc E u)
        (Matrix.GeneralLinearGroup.map (pFin E) x.1) :=
      Units.ext (Matrix.ext fun i j => rfl)
    rw [h1, h0, map_one]
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hI : IsCompact (infU E a : Set (UA E a)) := isCompact_iff_compactSpace.2 inferInstance
  have hDc : IsCompact ((C ⊔ infU E a : Subgroup (UA E a)) : Set (UA E a)) := by
    rw [Subgroup.mul_normal]
    exact hC.compact.mul hI
  have hd : c * x ∈ C ⊔ infU E a :=
    Subgroup.mul_mem _ (le_sup_left (a := C) hc) (le_sup_right (a := C) hx)
  have e : γ = g * (c * x) * g⁻¹ := by rw [← mul_assoc, ← h, mul_inv_cancel_right]
  have hfo : IsOfFinOrder (c * x) := GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints E a _ hDc g (c * x) hd (e ▸ hγ)
  have hcx : cLoc u (c * x) = cLoc u c := by rw [map_mul, hxl, mul_one]
  have h1 : cLoc u c = 1 := hT c hc (hcx ▸ (cLoc u).isOfFinOrder hfo)
  have hγ1 : cLoc u γ = 1 := by
    rw [e, map_mul, map_mul, map_inv, hcx, h1, mul_one, mul_inv_cancel]
  obtain ⟨γ₀, hγ₀⟩ : γ.1 ∈ (ratGL E a).range := Subgroup.mem_subgroupOf.1 hγ
  have hent : ∀ i j, algebraMap E (u.adicCompletion E) (γ₀.val i j) = (cLoc u γ).val i j := by
    intro i j
    change _ = pLoc E u (pFin E (γ.1.val i j))
    rw [← hγ₀]
    rfl
  have hγ₀1 : γ₀ = 1 := by
    refine Units.ext (Matrix.ext fun i j => (algebraMap E (u.adicCompletion E)).injective ?_)
    rw [hent, hγ1]
    simp [Matrix.one_apply, apply_ite (algebraMap E (u.adicCompletion E))]
  have hγe : γ = 1 := Subtype.ext (by rw [← hγ₀, hγ₀1, map_one]; rfl)
  have hcx1 : c * x = 1 := by
    rw [hγe, one_mul] at h
    have : g * (c * x) = g * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
    exact mul_left_cancel this
  have hf := congrArg GlobalTheory.EllU.finPart hcx1
  rwa [map_mul, GlobalTheory.EllU.finPart_of_finU (hC.fin hc), GlobalTheory.EllU.finPart_of_infU hx, mul_one, map_one] at hf
