import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSchemeOfSmoothOverNormal

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

theorem exists_torus_hom_extension : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i₀ : splitTorus (Sp K) X ⟶ (Over.pullback x).obj G) [IsMonHom i₀],
    ∃ (i : splitTorus C X ⟶ G) (ψ : (splitTorus (Sp K) X).left ⟶ (splitTorus C X).left), IsMonHom i ∧
      IsGrpPullback (splitTorus (Sp K) X) (splitTorus C X) x ψ ∧ ψ ≫ i.left = i₀.left ≫ pullback.fst G.hom x := by
  intro k _ C _ hC K _ x hx G _ hG X _ _ _ i₀ _
  obtain ⟨hs, -, hc⟩ := hC
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  have : Smooth (strHom k C) := SmoothOfRelativeDimension.smooth 1 _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  have hN : Geo.Tor.IsNormalScheme C :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension (Sp k) C (strHom k C) 1
      (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec k)
  obtain ⟨hxd, hxp⟩ := hx
  have hj : IsGenericPointHom x := IsGenericPointHom.of_isPreimmersion x
  have hT := GlobalTheory.Diag.isSemiAbelian C X
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian (splitTorus C X) hT
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have := hT.quasiCompact
  have := hG.smooth
  have hφ := GlobalTheory.Diag.isGrpPullback X x
  obtain ⟨V, hV, -, g, hg, w, h₁, h₂⟩ :=
    spread_hom_generic_of_isGrpPullback hj hφ (isGrpPullback_pullback G x) i₀
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact V.isOpen.dense ⟨_, hV⟩⟩
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.homExtNormal C V V.ι hN inferInstance inferInstance (splitTorus C X) G hT hG g hg
  refine ⟨F, _, hF, hφ, ?_⟩
  rw [← h₂, ← hF', GlobalTheory.ExtUnique.pullback_map_left_fst, ← h₁]
  exact Category.assoc _ _ _

end GlobalTheory.NeronCurve
