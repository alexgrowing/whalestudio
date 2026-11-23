import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tmap_injective_card_coker_of_isIsogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧
      Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  intro K _ l _ hl A B f hf
  have hsurj : Function.Surjective (ptMap f) := (surjective_iff_ptMap_surjective K A B f).1 hf.2
  have hfin : Finite (ptMap f).ker := (isFinite_iff_finite_ker K A B f).1 hf.1
  have hdiv : ∀ x : A.Pt, ∃ y, y ^ l = x := pt_divisible K A l (Fact.out : l.Prime).ne_zero
  obtain ⟨h1, h2⟩ := GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card l A.Pt B.Pt (ptMap f) hdiv hsurj hfin
  exact ⟨h1, h2.trans (GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree K l hl A B f hf)⟩

end GlobalTheory.AV.AbVar
