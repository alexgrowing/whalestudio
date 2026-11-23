import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringRatFuncXResidueZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuativeCriterionVarietiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearedGenericFlagEqGenericFlagAtSpecialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOfDominantPointAsTriangularMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixElementaryShearPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.Gen

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap g = spMap (h.comp g) := by
  rw [← Spec.map_comp]
  rfl

theorem exists_genPair : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ B ∈ E'.S (genericPoint Y.X), ∀ (τ : ι) (a b : Fin (m τ)), a < b → ∃ ψ₂ : Y.Fn →+* RatFunc Y.Fn, GenPair Y (algebraMap Y.Fn (RatFunc Y.Fn)) ψ₂ ∧ (∀ u : X.Fn, algebraMap Y.Fn (RatFunc Y.Fn) (φ u) = ψ₂ (φ u)) ∧ Par m ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) * (B.map (algebraMap Y.Fn (RatFunc Y.Fn)) * (B.map ψ₂)⁻¹)) := by
  intro F _ X Y ι _ m E E' φ f hf B hB τ a b hab
  obtain ⟨V, c, t, hc, ht, hr⟩ := GlobalTheory.T.exists_valuationSubring_ratFunc_X_residue_zero Y.Fn
  obtain ⟨A, hA⟩ := E.nonempty (f (genericPoint Y.X))
  have hM : Par 0 ((ratOf Y).O (genericPoint Y.X)).toSubring (B * (A.map φ)⁻¹) := hf.sub _ B hB A hA
  obtain ⟨pt, hpt⟩ : ∃ pt : Sp Y.Fn ⟶ Y.X, pt = (ratOf Y).pt := ⟨_, rfl⟩
  have hpa (w) : pt w = genericPoint Y.X := hpt ▸ (ratOf Y).pt_apply w
  have hps : pt ≫ Y.str = spMap (algebraMap F Y.Fn) := hpt ▸ (ratOf Y).pt_s
  have hq : spMap (algebraMap V (RatFunc Y.Fn)) ≫ spMap c ≫ pt = spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt := by
    rw [← Category.assoc, spMap_comp, hc]
  have hh : Par 0 ⊤ (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) := by
    refine Par.mul (ClosedPt.par_zero_top fun σ => ?_) (hM.map _ fun _ _ => trivial)
    rw [(GlobalTheory.T.blockMatrixElementaryShear_properties ι m τ a b hab _ _).1 σ]
    exact one_ne_zero
  have hx : ((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn)) = f (genericPoint Y.X) :=
    congrArg f (hpa _)
  have hA' : A ∈ E.S (((spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f)
      (IsLocalRing.closedPoint (RatFunc Y.Fn))) := (congrArg (fun z : X.X => A ∈ E.S z) hx).mpr hA
  obtain ⟨q₂, hq₂, hb⟩ : ∃ q₂ : Sp (RatFunc Y.Fn) ⟶ Y.X,
      q₂ ≫ f = (spMap (algebraMap Y.Fn (RatFunc Y.Fn)) ≫ pt) ≫ f ∧ Bears E' φ A (shear τ a b (RatFunc.X : RatFunc Y.Fn) *
      (B * (A.map φ)⁻¹).map (algebraMap Y.Fn (RatFunc Y.Fn))) q₂ := (hf.lifts (RatFunc Y.Fn) _ A hA' _ hh).exists
  have hs : f ≫ X.str = Y.str := hf.hom.inducedModelMorphism_comp_structureMap
  obtain ⟨v₂, hv₂, hv₂f⟩ := GlobalTheory.T.exists_lift_valuative_criterion_varieties F X Y f hs _ V (spMap c ≫ pt) q₂ (by
    rw [hq₂, ← hq]; simp only [Category.assoc])
  have hmeet : spMap (IsLocalRing.residue V) ≫ spMap c ≫ pt = spMap (IsLocalRing.residue V) ≫ v₂ := by
    subst hpt
    exact GlobalTheory.T.shearedGenericFlag_eq_genericFlag_at_special F X Y ι m E E' φ f hf B hB A hA τ a b hab _ V c t hr v₂
      (hv₂f.trans (Category.assoc _ _ _)) (by subst hv₂; rw [hc, ht]; exact hb)
  have h1 : (spMap c ≫ pt) (IsLocalRing.closedPoint V) = genericPoint Y.X := hpa _
  have h2 : v₂ (IsLocalRing.closedPoint V) = genericPoint Y.X := by
    rw [← ClosedPt.closedPt_comp v₂, ← hmeet, ClosedPt.closedPt_comp, h1]
  letI : Algebra F (RatFunc Y.Fn) := ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)).toAlgebra
  have hsp : q₂ (IsLocalRing.closedPoint (RatFunc Y.Fn)) ⤳ genericPoint Y.X := by
    have := ClosedPt.gen_specializes v₂ (IsLocalRing.closedPoint (RatFunc Y.Fn))
    rwa [hv₂, h2] at this
  have hstr : q₂ ≫ Y.str = spMap ((algebraMap Y.Fn (RatFunc Y.Fn)).comp (algebraMap F Y.Fn)) := by
    rw [← hs, ← Category.assoc, hq₂, Category.assoc, hs, Category.assoc, ← spMap_comp, hps]
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_specializes_genericPoint F Y (RatFunc Y.Fn) q₂ hsp hstr
  subst hpt
  have hcv := GlobalTheory.T.flag_of_dominant_point_as_triangular_matrix F X Y ι m E E' φ f hf B hB A hA _ (algebraMap Y.Fn (RatFunc Y.Fn)) ψ.toRingHom
    (shear τ a b RatFunc.X) (by
      subst hψ
      exact (Category.assoc _ _ _).symm.trans (hq₂.symm.trans (Category.assoc _ _ _))) (by subst hψ; exact hb)
  refine ⟨ψ.toRingHom, ⟨?_, V, spMap c ≫ (ratOf Y).pt, v₂, hq, hv₂.trans hψ, hmeet, h1⟩, hcv.1, hcv.2⟩
  exact RingHom.ext fun r => (ψ.commutes r).symm

end GlobalTheory.FlagPush.Gen
