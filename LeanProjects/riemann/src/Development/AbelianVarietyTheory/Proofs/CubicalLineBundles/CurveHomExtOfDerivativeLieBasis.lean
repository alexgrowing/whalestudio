import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomUnique

theorem hom_ext_of_lieBasis : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P Q : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (f f' : P.A ⟶ Q.A), (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom f → IsMonHom f' → v ≫ f = v ≫ f' → f = f' := by
  intro hU hB k _ s P Q v f f' hv hf hf' h
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB s P
  obtain ⟨Q', ψ, hQ⟩ := exists_isPolFibre hB s Q
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hP.2.1.1 v
  obtain ⟨g, hg, eg⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f
  obtain ⟨g', hg', eg'⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f'
  have hb := hv ℂ s P' φ v' hP hv'
  have e₁ : v' ≫ g = v' ≫ g' := by
    refine Over.OverMorphism.ext (hQ.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have hl : v.left ≫ f.left = v.left ≫ f'.left := congrArg (fun z => z.left) h
    unfold IsVecOver at hv'
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, eg, eg', ← Category.assoc, ← Category.assoc,
      hv', Category.assoc, Category.assoc, hl]
  have e₂ : g = g' := by
    refine (HomDescent.pol_countable_and_tangent_ext hU P' Q').2 g g' hg hg' fun x hx => ?_
    obtain ⟨c, hc, -⟩ := hb.2 x hx
    have ec : c = ![c 0] := by
      ext i
      fin_cases i
      rfl
    rw [ec, LieMultiple.isLieComb_one_iff_comp] at hc
    rw [hc, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e₁
  have := P.isAb.smooth
  have := Q.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap s) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom s) s.injective
  exact ExtUnique.over_hom_ext_of_isPullback hP.2.1.1 (by rw [← eg, ← eg', e₂])

end GlobalTheory.HomUnique
