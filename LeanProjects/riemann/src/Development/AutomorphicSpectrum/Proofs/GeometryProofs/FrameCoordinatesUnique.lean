import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactorStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaFunctionsFiniteDimStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogenyStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameVec

open GlobalTheory.CompanionTheory.Ar.LieSigma

theorem one_left_over {S : Scheme.{0}} {X M : Over S} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem isVec_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ), (∀ v, IsTangent v → ∃! w, a.u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ a.u.IsDiff w v) → ∀ x : D.B.carrier, ∃! c, D.IsVec a x c := by
  intro E _ _ _ H L _ _ D σ a h1 h2 x
  have hpull := isTanAt_pull D.t.G (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) (D.MB.pt x) (D.MB.tan x)
  have hw : (spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ≫ D.t.G.hom
      = (epsAt (emb σ)).hom := by
    have := Over.w (pullEps (σ.comp (algebraMap (𝓞 L) L)) (𝟙 _) ≫ D.MB.pt x)
    simpa [pullEps] using this
  let v : epsAt (emb σ) ⟶ D.t.G := Over.homMk _ hw
  have hvl : v.left = spMap (dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left := rfl
  have hlift : D.MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 D.t.G.left) x v := by
    show v.left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact hvl
  have hsq : v.left ≫ D.t.G.hom = (epsR ℂ).hom ≫ emb σ := hw
  let v' : epsR ℂ ⟶ a.A := Over.homMk (a.cart.1.lift v.left (epsR ℂ).hom hsq) (a.cart.1.lift_snd _ _ _)
  have hφ : v'.left ≫ a.φ = v.left := a.cart.1.lift_fst _ _ _
  have ht : IsTangent v' := by
    unfold IsTangent
    apply a.cart.1.hom_ext
    · have h3 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = _ := hpull
      rw [Category.assoc, hφ, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left a.cart, h3, one_left_over]
      simp
    · have e : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (epsR ℂ).hom = 𝟙 _ := by
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
          ext t <;> simp
        rw [this]
        exact Spec.map_id _
      rw [Category.assoc, Over.w v', e]
      simpa using (Over.w η[a.A]).symm
  obtain ⟨c, hc, hu⟩ := h1 v' ht
  refine ⟨c, ⟨v, hlift, v', hφ, hc⟩, ?_⟩
  rintro c' ⟨v₁, hl₁, v₁', hφ₁, hc₁⟩
  have e₁ : v₁.left = v.left := by
    have : v₁.left ≫ 𝟙 _ = _ := hl₁
    rw [Category.comp_id] at this
    exact this
  have e₂ : v₁' = v' := by
    apply Over.OverMorphism.ext
    apply a.cart.1.hom_ext
    · rw [hφ₁, hφ, e₁]
    · rw [Over.w v₁', Over.w v']
  exact hu c' (e₂ ▸ hc₁)

end GlobalTheory.CompanionTheory.Ar.Sl.FrameVec
