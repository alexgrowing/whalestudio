import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqMulOfRankAtStalk
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_comp_and_deg_comp : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C),
    IsIsogeny f → IsIsogeny g → IsIsogeny (f ≫ g) ∧ deg (f ≫ g) = deg f * deg g := by
  intro K _ A B C f g hf hg
  obtain ⟨-, hflf, -, hrf⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨-, hflg, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K B C g hg
  have : IsFinite f.hom.left := hf.1
  have : Surjective f.hom.left := hf.2
  have : IsFinite g.hom.left := hg.1
  have : Surjective g.hom.left := hg.2
  have hc : IsIsogeny (f ≫ g) := by
    refine ⟨?_, ?_⟩
    · rw [comp_hom, Over.comp_left]; infer_instance
    · rw [comp_hom, Over.comp_left]; infer_instance
  refine ⟨hc, ?_⟩
  have hdg : deg g = g.hom.left.finrank C.origin := if_pos hg
  have hdc : deg (f ≫ g) = (f ≫ g).hom.left.finrank C.origin := if_pos hc
  rw [hdc, hdg, comp_hom, Over.comp_left]
  exact GlobalTheory.FinrankComp.finrank_comp_of_const f.hom.left g.hom.left (deg f) hrf C.origin

end GlobalTheory.AV.AbVar
