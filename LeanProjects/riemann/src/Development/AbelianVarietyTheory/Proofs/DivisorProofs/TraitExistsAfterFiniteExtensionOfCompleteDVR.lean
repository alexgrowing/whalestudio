import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianSemiAbelianSiegelPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtensionSiegelFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialPeriodsSymmetricExponentFormStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem traitExtSt_of (h₁ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
      GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
        ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
          (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
          ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
            IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
            ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
              IsSemiAbelian G ∧ IsMonHom gen.hom)
    (h₂ : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V₁ : Type) [CommRing V₁] [IsDomain V₁]
      [IsLocalRing V₁], GlobalTheory.LN.CDvr V₁ → ∀ (y₁ : Sp (FractionRing V₁) ⟶ F.X) (A : PolAV (Sp (FractionRing V₁)))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      IsGrpPullback A.A F.univ.A y₁ α → IsSquare α α₂ → LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) →
      ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G] (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
      IsSemiAbelian G → IsMonHom gen.hom →
        ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V₁ →+* W)
          (fK : FractionRing V₁ →+* FractionRing W), GlobalTheory.LN.CDvr W ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
          (∀ a, fK (algebraMap V₁ _ a) = algebraMap W _ (f a)) ∧
          ∃ (G' : Over (Sp W)) (_ : GrpObj G') (_ : IsCommMonObj G') (D : DegData W (maximalIdeal W))
            (A' : PolAV (Sp (FractionRing W))) (_ : Unif (maximalIdeal W) D A' G') (α' : A'.A.left ⟶ F.univ.A.left)
            (α₂' : (G2 A'.A).left ⟶ (G2 F.univ.A).left),
            IsSemiAbelian G' ∧ IsGrpPullback A'.A F.univ.A (spMap fK ≫ y₁) α' ∧ IsSquare α' α₂' ∧
            LBIso (abelian₂ A'.A A'.L) (F.univ.P.pull α₂'))
    (h₃ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ϖ : W, Irreducible ϖ →
      ∀ D : DegData W (maximalIdeal W), ∃ β : LinearMap.BilinForm ℤ D.toPre.X, (∀ a b, β a b = β b a) ∧
        IsMonomial D.toPre ![ϖ] ![β]) : TraitExtSt := by
  intro g n o _ ζ F V _ _ _ hB hD y
  obtain ⟨V₁, _, _, _, f, fK, hC₁, hinj₁, hloc₁, hfin₁, hK₁, A, α, α₂, hcart, hsq, hlb, G, _, _, gen, hsemi, hmon⟩ :=
    h₁ g n o ζ F V hB hD y
  obtain ⟨W, _, _, _, f', fK', hCW, hinj₂, hloc₂, hfin₂, hK₂, G', _, _, D, A', U, α', α₂', hsemi', hcart', hsq', hlb'⟩ :=
    h₂ g n o ζ F V₁ hC₁ (spMap fK ≫ y) A α α₂ hcart hsq hlb G gen hsemi hmon
  obtain ⟨hdvr, hcpl, hchar⟩ := hCW
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨β, hβs, hβm⟩ := h₃ W ⟨hdvr, hcpl, hchar⟩ ϖ hϖ D
  have hsp : spMap (fK'.comp fK) = spMap fK' ≫ spMap fK := by
    unfold spMap
    simp
  refine ⟨
    { V := W
      complete := hcpl
      ϖ := ϖ
      irr := hϖ
      y := spMap (fK'.comp fK) ≫ y
      G := G'
      semi := hsemi'
      D := D
      A := A'
      U := U
      α := α'
      α₂ := α₂'
      cart := ?_
      sq := hsq'
      lb := hlb'
      β := β
      symm := hβs
      mono := hβm },
    f'.comp f, fK'.comp fK, hinj₂.comp hinj₁, ?_, hfin₂.comp hfin₁, ?_, rfl⟩
  · rw [hsp, Category.assoc]
    exact hcart'
  · exact RingHom.isLocalHom_comp f' f
  · intro a
    simp [hK₁, hK₂]

theorem traitExtSt : TraitExtSt :=
  traitExtSt_of GlobalTheory.T.exists_polarisedAbelian_semiAbelian_siegelPoint GlobalTheory.T.exists_uniformisation_finiteExtension_siegelFamily GlobalTheory.T.exists_monomialPeriods_symmetric_exponentForm

end GlobalTheory.Poinc
