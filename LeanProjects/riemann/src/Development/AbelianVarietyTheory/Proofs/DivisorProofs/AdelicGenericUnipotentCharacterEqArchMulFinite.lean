import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem adele_eq_sInf_add_sFin {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Ad E) :
    x = sInf E (pInf E x) + sFin E (pFin E x) := by
  refine Prod.ext ?_ ?_
  · change x.1 = infEq E ((infEq E).symm x.1) + 0
    simp
  · change x.2 = 0 + x.2
    simp

theorem psiN_split : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  intro E _ _ _ n u
  have h : GlobalTheory.Whittaker.superDiag u = sInf E (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) + sFin E (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
    simp only [GlobalTheory.Whittaker.superDiag, sdM, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact adele_eq_sInf_add_sFin _
  unfold GlobalTheory.JSW.psiN psiInf psiFin
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.WhitBump
