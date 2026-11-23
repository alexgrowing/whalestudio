import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD GlobalTheory.ThetaPull GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.DualSm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in

theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  change p ((g⁻¹).val j i) = (GeneralLinearGroup.map p g)⁻¹.val j i
  rw [← map_inv]
  rfl

theorem invA_infGL (y : GL (Fin a) (Cinf E)) :
    invA E a (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [invA, map_invT, pInf_infGL, pInf_infGL])
    (by rw [invA, map_invT, pFin_infGL, pFin_infGL, map_one])

omit [NumberField E] [IsTotallyComplex E] in

def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

omit [IsTotallyComplex E] in

theorem toL_invT (y : GL (Fin a) (Cinf E)) : toL (invT a (Cinf E) y).val = trL (invL (toL y.val)) := by
  change toL ((y⁻¹).val)ᵀ = toL (Matrix.of (toL (Matrix.of (toL y.val))⁻¹))ᵀ
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_dual (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invA E a g))) g x = star (chart φ (invA E a g) (trL (invL x))) ∧
      trL (invL x) ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem conj_invA_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun g => star (φ (invA E a g))) ∈ Sm E a := fun g =>
  (Complex.conjCLE.contDiff.comp_contDiffOn ((hφ (invA E a g)).comp
    (fun x hx => (trL.contDiff.contDiffAt.comp x (invL_smooth.1 x hx)).contDiffWithinAt)
    fun _ hx => (chart_dual φ g hx).2)).congr fun _ hx => (chart_dual φ g hx).1

end GlobalTheory.CompanionTheory.DualSm

end
