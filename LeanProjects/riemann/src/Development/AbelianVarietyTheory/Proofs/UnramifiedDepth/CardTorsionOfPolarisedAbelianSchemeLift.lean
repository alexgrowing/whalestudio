import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem card_torsion_of_isGrpPullback : ∀ (R O C : Type) [CommRing R] [CommRing O] [Field C] [IsAlgClosed C] [Algebra R O] [Algebra O C] [Algebra R C] [IsScalarTower R O C] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : Out.PolAV (Geo.Tor.Sp O)) (ψ : P.A.left ⟶ G.left), Geo.Tor.IsGrpPullback P.A G (Spec.map (CommRingCat.ofHom (algebraMap R O))) ψ → ∀ n : ℕ, (n : C) ≠ 0 → Nat.card {z : sp (R₀ := R) C ⟶ G // z ^ n = 1} = n ^ (2 * P.g) := by
  intro R O C _ _ _ _ _ _ _ _ G _ _ P ψ h n hn
  let t : Geo.Tor.Sp C ⟶ Geo.Tor.Sp O := Spec.map (CommRingCat.ofHom (algebraMap O C))
  rw [← GlobalTheory.ArcExt.card_torsion GlobalTheory.firstFiveLaws.1 P t hn]
  have hc : t ≫ Spec.map (CommRingCat.ofHom (algebraMap R O)) = (sp (R₀ := R) C).hom := by
    show _ = Spec.map (CommRingCat.ofHom (algebraMap R C))
    rw [IsScalarTower.algebraMap_eq R O C, CommRingCat.ofHom_comp, Spec.map_comp]
  let ρ : sp (R₀ := R) C ⟶ Over.mk ((Over.mk t).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R O))) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hc)
  let Φ : (Over.mk t ⟶ P.A) →* (sp (R₀ := R) C ⟶ G) :=
    (Geo.Tor.preHom ρ).comp (Geo.Tor.pushHom h (Over.mk t))
  have hΦ : ∀ x, (Φ x).left = x.left ≫ ψ := fun x => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm)), fun a => ?_⟩
    · rw [← hΦ, ← hΦ, e]
    · exact ⟨Over.homMk (h.1.lift a.left t ((Over.w a).trans hc.symm)) (h.1.lift_snd _ _ _),
        Over.OverMorphism.ext ((hΦ _).trans (h.1.lift_fst _ _ _))⟩
  let e := MulEquiv.ofBijective Φ hb
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    show _ ↔ e x ^ n = 1
    rw [← map_pow, EmbeddingLike.map_eq_one_iff])).symm

end GlobalTheory.ChF
