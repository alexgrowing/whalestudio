import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

private theorem theta_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {P : CuspSub E a} (h : P.IsCsd) :
    (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  obtain ⟨T, hT⟩ := h
  let L := (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V
  refine ⟨L.symm.trans T, fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := L.surjective φ
  have e : (GlobalTheory.ThetaPull.thetaSub P).op o (L φ) = L (P.op (thetaOp o) φ) :=
    Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
  rw [e]
  exact (congrArg T (L.symm_apply_apply _)).trans
    ((hT o φ).trans (congrArg (P.op o) (congrArg T (L.symm_apply_apply φ)).symm))

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (Bc.cPl w) = normV w := by
  change Nat.card (𝓞 E ⧸ (Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

private theorem qPow_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (s : ℝ) :
    (qPow (Bc.cPl w) s)⁻¹ = qPow w (-s) := by
  have e : qPow (Bc.cPl w) s = qPow w s := Units.ext (by rw [coe_qPow, coe_qPow, normV_cPl])
  rw [e, inv_eq_iff_mul_eq_one, ← qPow_add, add_neg_cancel, qPow_zero]

theorem UpperTheory.satake_parameters_complex_conjugate :
    SatConj := by
  intro E _ _ _ w
  refine ⟨fun a P hP B hB => ?_, fun c d S => ?_⟩
  · have e : CG.mk (GlobalTheory.ThetaPull.thetaSub P) = CG.mk P := Quotient.sound (theta_iso hP)
    exact e ▸ UpperTheory.theta_satake_parameters_inverse E a P w B hB
  · unfold satTot
    rw [← Multiset.coe_mapAddMonoidHom (fun x : ℂˣ => x⁻¹), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply, mul_inv, qPow_cPl, Fin.revPerm_apply, Fin.val_rev]
    congr 2
    rw [Nat.cast_sub k.2]
    push_cast
    ring
