import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineRefinementAlongMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPairInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionPairPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionRefineFinerBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionEqOfIsoStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBObs

theorem lineBundleLiftObstruction_natural_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L L' c c' hL hL' hiso hc hc'
  obtain ⟨C, _, _, G, hGb, hG⟩ := hc
  obtain ⟨C', _, _, G', hG'b, hG'⟩ := hc'
  obtain ⟨D, _, _, K, H, H', ⟨θ⟩, ⟨θ'⟩, hKb⟩ := GlobalTheory.T.exists_common_affine_refinement_along_morphism X₀ Z₀ f₀ C C' G G' hGb hG'b
  have h1 := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α X₀ s₀ S L c C D G (K ⋙ pairSnd f₀) H θ hG
  have h2 := GlobalTheory.T.lineBundleLiftObstruction_pairPullback R R₀ I hI π hπ hk R₁ α X₀ Z₀ s₀ t₀ S S' f₀ h l hl hn L c D K h1
  have h3 := GlobalTheory.T.lineBundleLiftObstruction_refine_finerBasis R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' c' C' D G' (K ⋙ pairFst f₀) H' θ' hG'
  have h4 := GlobalTheory.T.lineBundleLiftObstruction_eq_of_iso R R₀ I hI π hπ hk R₁ α Z₀ t₀ S' L' (L.pull f₀) D (K ⋙ pairFst f₀) _ _ hL'
    (pull_isLB hL f₀) hiso h3 h2
  apply GlobalTheory.LBObs.PairInj.restrict_pair_injective R₀ R₁ X₀ Z₀ t₀ f₀ D K hKb
  refine h4.symm.trans ?_
  have e : ∀ {E : Type} [Category.{0} E] {E' : Type} [Category.{0} E'] (F : E ⥤ CommAlgCat.{0} R₀) (G : E' ⥤ E)
      (T : E') (x : R₁ ⊗[R₀] F.obj (G.obj T)), (extMap R₁ (CoefMap.restrict F G)).α T x = x := by
    intro E _ E' _ F G T x
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul y b => rfl
    | add x y hx hy => exact (map_add _ x y).trans (congrArg₂ (· + ·) hx hy)
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c'
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  congr 1
  refine Subtype.ext ?_
  funext T T' T'' φ ψ
  exact (e _ _ _ _).trans ((e (OPair f₀ t₀) K _ _).trans (e (OAff t₀) (pairFst f₀) _ _)).symm

end GlobalTheory.LBObs
