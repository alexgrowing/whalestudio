import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam

namespace GlobalTheory.AmpleKaehler

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def pullW (Z : TrueGeo.Model Y) (L : HermLB Z.p) (σ : F →+* ℂ) : Weight Y.str σ (L.B.pull Z.j) :=
  (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => OfModel.ptMap Z σ) fun _ _ => rfl

variable (Z : TrueGeo.Model Y) (L : HermLB Z.p)

theorem pullW_φ (σ : F →+* ℂ) (i : (L.B.pull Z.j).ι) (y : Pts Y σ) :
    (pullW Z L σ).φ i y = (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ (i PUnit.unit) (OfModel.ptMap Z σ y) :=
  (Fintype.sum_unique fun a : PUnit.{1} =>
    ((1 : ℤ) : ℝ) * (L.φ (σ.comp (algebraMap (𝓞 F) F))).φ (i a) (OfModel.ptMap Z σ y)).trans (by simp)

theorem pullW_isConj (σ σ' : F →+* ℂ) : (pullW Z L σ').IsConj (pullW Z L σ) := by
  intro i y y' hy hi
  rw [pullW_φ, pullW_φ]
  refine L.conj (σ'.comp (algebraMap (𝓞 F) F)) (σ.comp (algebraMap (𝓞 F) F)) (i PUnit.unit)
    (OfModel.ptMap Z σ' y) (OfModel.ptMap Z σ y') ?_
    (mem_of_mem_linComb (m := fun _ => OfModel.ptMap Z σ' y) (fun _ => rfl) hi PUnit.unit)
  change y'.1 ≫ Z.j = spMap (starRingEnd ℂ) ≫ y.1 ≫ Z.j
  rw [hy, Category.assoc]

end GlobalTheory.AmpleKaehler
