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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifCompareIsogeny
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl.TanIso

open GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A']

theorem isTangent_comp (f : A' ⟶ A) [IsMonHom f] {v : epsR ℂ ⟶ A'} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  have h₁ : η[A'] ≫ f = η[A] := IsMonHom.one_hom f
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, h₁]

theorem linLift_injective {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (e : A' ≅ A) [IsMonHom e.hom] (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u'.ex z ≫ e.hom) :
    Function.Injective F := by
  refine (injective_iff_map_eq_zero F).2 fun z hz => ?_
  have hone : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ e.hom) = 1 := by rw [MonObj.one_comp]
  have hmem : ∀ c : ℂ, c • z ∈ u'.Λ := fun c => by
    refine (u'.ker _).1 ?_
    have h0 : u'.ex (c • z) ≫ e.hom = 1 := by
      rw [← hF, map_smul, hz, smul_zero]
      exact (u.ker 0).2 u.Λ.zero_mem
    have : (u'.ex (c • z) ≫ e.hom) ≫ e.inv = ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ e.hom) ≫ e.inv := by rw [h0, hone]
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using this
  haveI := u'.discrete
  let φ : ℂ → u'.Λ := fun c => ⟨c • z, hmem c⟩
  have hφ : Continuous φ := Continuous.subtype_mk (continuous_id.smul continuous_const) _
  have h := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hφ (x := 1) (y := 0)
  simpa [φ] using congrArg Subtype.val h

theorem isDiff_of_comp {M : LB A.left} {M' : LB A'.left} {g g' : ℕ} (u : HolUnif A M g) (u' : HolUnif A' M' g')
    (e : A' ≅ A) [IsMonHom e.hom] (F : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, u.ex (F z) = u'.ex z ≫ e.hom)
    {c : Fin g' → ℂ} {v : epsR ℂ ⟶ A'} (ht : IsTangent v) (hd : u.IsDiff (F c) (v ≫ e.hom)) : u'.IsDiff c v := by
  have a0 := isDerivAt0_of_isDiff u (isTangent_comp e.hom ht) hd
  have a1 := isDerivAt0_comp_linMap (isHolTo_ex u) F a0
  have a2 := GlobalTheory.FibreDeriv.isDerivAt0_comp a1 e.inv.left
  have l₁ : (v ≫ e.hom).left ≫ e.inv.left = v.left := by
    rw [← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [l₁, show (fun z => (u.ex (F z)).left ≫ e.inv.left) = fun z => (u'.ex z).left from funext fun z => by
    rw [← Over.comp_left, hF, Category.assoc, e.hom_inv_id, Category.comp_id]] at a2
  exact fun U h f => a2.2 U h f

theorem tangentCoords_of_iso : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (M : LB A.left) (M' : LB A'.left) (g : ℕ) (u : HolUnif A M g) (u' : HolUnif A' M' g) (e : A' ≅ A) [IsMonHom e.hom], IsAbelianScheme A → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u'.IsDiff w v) := by
  intro A A' _ _ M M' g u u' e _ hAb d₁ d₂
  have hol : IsHolTo (Set.univ : Set (Fin g → ℂ)) (fun w => (u'.ex w ≫ e.hom).left) := by
    simpa only [Over.comp_left] using GlobalTheory.HolTorsion.isHolTo_comp (isHolTo_ex u') e.hom.left
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo A hAb M g g u d₁ d₂
    (fun w => u'.ex w ≫ e.hom) (fun p q => by rw [u'.ex_add, MonObj.mul_comp]) hol
  have hinj : Function.Injective F := linLift_injective u u' e F hF
  have hsurj : Function.Surjective F := LinearMap.injective_iff_surjective.1 hinj
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · obtain ⟨w₀, hw₀, huniq⟩ := d₁ _ (isTangent_comp e.hom hv)
    obtain ⟨c, rfl⟩ := hsurj w₀
    refine ⟨c, isDiff_of_comp u u' e F hF hv hw₀, fun c' hc' => hinj (huniq _ ?_)⟩
    exact GlobalTheory.CompanionTheory.Ar.HodgeUniq.isDiff_comp u u' d₂ e.hom F hF hv hc'
  · obtain ⟨t, ⟨ht, hd⟩, huniq⟩ := d₂ (F w)
    have hcomp : (t ≫ e.inv) ≫ e.hom = t := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    have hv : IsTangent (t ≫ e.inv) := GlobalTheory.CompanionTheory.Ar.HodgeUniq.tangent_of_iso e ht hcomp
    refine ⟨t ≫ e.inv, ⟨hv, isDiff_of_comp u u' e F hF hv (hcomp.symm ▸ hd)⟩, fun v' hv' => ?_⟩
    have h := huniq (v' ≫ e.hom) ⟨isTangent_comp e.hom hv'.1,
      GlobalTheory.CompanionTheory.Ar.HodgeUniq.isDiff_comp u u' d₂ e.hom F hF hv'.1 hv'.2⟩
    rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

end GlobalTheory.CompanionTheory.Ar.Sl.TanIso
