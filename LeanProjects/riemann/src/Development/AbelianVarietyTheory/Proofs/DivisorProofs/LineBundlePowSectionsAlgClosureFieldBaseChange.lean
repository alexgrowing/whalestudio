import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

section
variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))

theorem noetherianSpace_prod_field (F : Type) [Field F] [Algebra (FractionRing R) F] :
    TopologicalSpace.NoetherianSpace (TFK (R := R) F ⊗ A.A).left := by
  have := A.isAb.proper
  let b : (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left
  have : IsProper b := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) F ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian b
  have : CompactSpace (TFK (R := R) F ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace b
  have : IsNoetherian (TFK (R := R) F ⊗ A.A).left := {}
  infer_instance

theorem isPullback_baseEm_whiskerRight {F : Type} [Field F] [Algebra (FractionRing R) F]
    (em : Kb R →ₐ[FractionRing R] F) :
    IsPullback (baseEm em ▷ A.A).left (fst (TFK (R := R) F) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      (baseEm em).left := by
  have h₁ : IsPullback (snd (TFK (R := R) (Kb R)) A.A).left (fst (TFK (R := R) (Kb R)) A.A).left
      A.A.hom (TFK (R := R) (Kb R)).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (fst (TFK (R := R) F) A.A).left
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (congrArg (fun q => q.left) (whiskerRight_fst (baseEm em) A.A)) h₁
  have e₁ : (baseEm em ▷ A.A).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (whiskerRight_snd (baseEm em) A.A)
  have e₂ : (baseEm em).left ≫ (TFK (R := R) (Kb R)).hom = (TFK (R := R) F).hom := Over.w (baseEm em)
  rw [e₁, e₂]
  exact h₂

end

theorem isExtension_secExt : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), letI : Algebra (Kb R) F := em.toRingHom.toAlgebra; GlobalTheory.FieldBaseChange.IsExtension (secExt A em N) := by
  intro R _ _ A F _ _ em N
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  have := noetherianSpace_prod_field A (Kb R)
  exact GlobalTheory.FieldBaseChange.isExtension_pullOver (K := Kb R) (F := F) (isPullback_baseEm_whiskerRight A em) A.isLB _ _

end GlobalTheory.Mum.Desc
