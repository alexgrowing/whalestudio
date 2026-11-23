import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.MixedLocalChains

theorem hom_ext_of_pullback_ι {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules}
    (h : GlobalTheory.VB.IsTorsionFree G) (a b : F ⟶ G) (U : X.Opens) (hU : genericPoint X ∈ U)
    (e : (Scheme.Modules.pullback U.ι).map a = (Scheme.Modules.pullback U.ι).map b) : a = b := by
  have hr : (Scheme.Modules.restrictFunctor U.ι).map a
      = (Scheme.Modules.restrictFunctor U.ι).map b := by
    rw [← cancel_mono ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app G),
      NatTrans.naturality, NatTrans.naturality, e]
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext s
  by_cases hη : genericPoint X ∈ W
  · have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ≤ W := U.ι.image_preimage_le W
    have hη' : genericPoint X ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) := ⟨⟨_, hU⟩, hη, rfl⟩
    have happ : a.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) = b.app (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) :=
      congrArg (fun φ => Scheme.Modules.Hom.app φ (U.ι ⁻¹ᵁ W)) hr
    refine sub_eq_zero.1 (h W hη _ ?_)
    have na := ConcreteCategory.congr_hom (a.mapPresheaf.naturality (homOfLE hle).op) s
    have nb := ConcreteCategory.congr_hom (b.mapPresheaf.naturality (homOfLE hle).op) s
    have e' : G.presheaf.map (homOfLE hle).op (a.app W s)
        = G.presheaf.map (homOfLE hle).op (b.app W s) :=
      na.symm.trans ((ConcreteCategory.congr_hom happ _).trans nb)
    rw [map_sub, sub_eq_zero]
    erw [← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (a.app W s),
      ← G.presheaf.germ_res_apply (homOfLE hle) _ hη' (b.app W s), e']
  · have hW : W = ⊥ := by
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty W).1 hne
      exact hη (GlobalTheory.VB.genericPoint_mem hx)
    subst hW
    exact TopCat.Sheaf.eq_of_locally_eq' ⟨G.presheaf, G.isSheaf⟩ (fun _ : Empty => ⊥) ⊥
      (fun i => i.elim) bot_le _ _ (fun i => i.elim)

theorem hom_ext_of_genRes : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (Z : GlobalTheory.Vert.Model O) (F G : Z.X.Modules) (m : ℕ) (a b : F ⟶ G),
    GlobalTheory.VB.IsVB G m → Z.genRes.map a = Z.genRes.map b → a = b :=
  fun _ _ _ _ Z _ _ _ a b hG e =>
    hom_ext_of_pullback_ι hG.isTorsionFree a b Z.gen Z.genericPoint_mem_gen e

end GlobalTheory.MixedLocalChains
