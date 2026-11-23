import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaPolarisationSiegelObjectCharZeroFielStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRFiniteMapOfFiniteAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.CExtGen

theorem exists_polAV_semiAbelian : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ F.X,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧
        ∃ (A : PolAV (Sp (FractionRing V₁))) (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
          IsGrpPullback A.A F.univ.A (spMap fK ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
          ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
            IsSemiAbelian G ∧ IsMonHom gen.hom := by
  intro g n o _ ζ F V _ _ _ hB hV y
  have hC : GlobalTheory.LN.CDvr V := ⟨hV, hB.1.2.2.2, hB.2⟩
  haveI : CharZero V := hB.2
  haveI : CharZero (FractionRing V) := inferInstance
  obtain ⟨R₁, _, _, hfin, hnt, P, α, α₂, hα, hsq, hlam⟩ := GlobalTheory.T.exists_lambdaPolarisation_siegelObject_charZeroField g n o ζ F.X F.s F.univ F.princ (FractionRing V) y
  obtain ⟨W₁, _, _, _, f₁, ψ, hW₁, hi₁, hl₁, hf₁, hc₁⟩ := GlobalTheory.T.exists_completeDVR_finite_map_of_finiteAlgebra V hC R₁ hfin hnt
  obtain ⟨P₁, φ₁, hP₁, -, hL₁⟩ := GlobalTheory.KeyFam.SameLam.exists_polPB P ψ
  obtain ⟨β₂, hβ₂, hΛ₁⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P.A P₁.A φ₁ hP₁
  have lam₁ := hΛ₁ P.L P₁.L _ F.univ.P α₂ P.isLB P₁.isLB F.univ.isLB hL₁ hlam
  obtain ⟨V₁, _, _, _, f₂, fK₂, hV₁, hi₂, hl₂, hf₂, hc₂, A, β, hβ, hLA, G, _, _, gen, hG, hgen⟩ := GlobalTheory.T.exists_semiAbelianModel_finiteExt_completeDVR W₁ hW₁ P₁
  obtain ⟨γ₂, hγ₂, hΛ₂⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ P₁.A A.A β hβ
  have lam₂ := hΛ₂ P₁.L A.L _ F.univ.P (β₂ ≫ α₂) P₁.isLB A.isLB F.univ.isLB hLA lam₁
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, f₂.comp f₁, fK₂.comp (ψ.comp (algebraMap _ R₁)), hV₁,
    hi₂.comp hi₁, ?_, hf₂.comp hf₁, ?_, A, β ≫ φ₁ ≫ α, γ₂ ≫ β₂ ≫ α₂, ?_, ?_, ?_, G, inferInstance, inferInstance, gen, hG,
    hgen⟩
  · exact RingHom.isLocalHom_comp f₂ f₁
  · intro a
    simp [hc₁, hc₂]
  · refine (hβ.comp (hP₁.comp hα)).congr ?_ rfl
    simp [spMap, Spec.map_comp]
  · exact GlobalTheory.ZM.SiegPull.isSquare_comp hγ₂ (GlobalTheory.ZM.SiegPull.isSquare_comp hβ₂ hsq)
  · simpa [Category.assoc] using lam₂

end GlobalTheory.CExtGen
