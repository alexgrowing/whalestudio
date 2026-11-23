import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.HtPt.Ppic

theorem exists_factor_torus {K : Type} [Field K] [IsAlgClosed K] {G B B' : Over (Sp K)} [GrpObj G] [GrpObj B] [GrpObj B']
    (hB' : IsAbelianScheme B') {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp K) X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Flat q.left] [Surjective q.left]
    [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (f : G ⟶ B') [IsMonHom f] :
    ∃ a : B ⟶ B', q ≫ a = f := by
  haveI : IsProper B'.hom := hB'.proper
  have hif : i ≫ f = toUnit _ ≫ η :=
    GlobalTheory.splitTorus_hom_proper_trivial_field K X B' (i ≫ f) inferInstance
  refine GlobalTheory.ExtensionRigidity.exists_factor q f ?_
  intro W a b hab
  have h1 := map_div (IsMonHom.monoidHom q W) a b
  simp only [IsMonHom.monoidHom_apply] at h1
  rw [hab, div_self'] at h1
  have hc : (a / b) ≫ q = toUnit W ≫ η := by rw [h1, Hom.one_def]
  have e2 : (a / b) ≫ f = 1 := by
    rw [← hk.lift_fst (a / b) (toUnit W) hc, Category.assoc, hif, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h3 := map_div (IsMonHom.monoidHom f W) a b
  simp only [IsMonHom.monoidHom_apply] at h3
  rw [e2] at h3
  exact div_eq_one.1 h3.symm

theorem quot : ∀ (G : Over (Sp ℂ)) [GrpObj G] [IsCommMonObj G] (τ : TorusExtension G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : GlobalTheory.UU.TQ G X), letI := τ.grpB; ∃ e : τ.B ≅ T.B, IsMonHom e.hom ∧ τ.q ≫ e.hom = T.q := by
  intro G _ _ τ X _ _ _ T
  letI := τ.grpB
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.q_hom
  haveI := τ.q_flat
  haveI := τ.q_surjective
  haveI := τ.q_quasiCompact
  haveI := τ.i_hom
  haveI := T.q_hom
  haveI := T.q_flat
  haveI := T.q_surj
  haveI := T.q_affine
  haveI := T.i_hom
  obtain ⟨a, ha⟩ := exists_factor_torus T.isAb τ.i τ.q τ.isKernel T.q
  obtain ⟨b, hb⟩ := exists_factor_torus τ.isAbelian T.i T.q T.isKernel τ.q
  haveI : Epi τ.q := Over.epi_of_epi_left _
  haveI : Epi T.q := Over.epi_of_epi_left _
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    { comp_mem := fun f g hf hg => by haveI := hf; haveI := hg; infer_instance }
  haveI : Epi (τ.q ⊗ₘ τ.q) := by
    haveI : Flat (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Flat) τ.q_flat τ.q_flat (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : Surjective (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @Surjective) τ.q_surjective τ.q_surjective
        (Over.w τ.q).symm (Over.w τ.q).symm
    haveI : QuasiCompact (τ.q ⊗ₘ τ.q).left :=
      MorphismProperty.pullbackMap (P := @QuasiCompact) τ.q_quasiCompact τ.q_quasiCompact
        (Over.w τ.q).symm (Over.w τ.q).symm
    exact Over.epi_of_epi_left _
  have hma : IsMonHom a := by
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom τ.q, Category.assoc, ha, IsMonHom.one_hom]
    · rw [← cancel_epi (τ.q ⊗ₘ τ.q), ← IsMonHom.mul_hom_assoc, ha, IsMonHom.mul_hom,
        tensorHom_comp_tensorHom_assoc, ha]
  refine ⟨⟨a, b, ?_, ?_⟩, hma, ha⟩
  · rw [← cancel_epi τ.q, reassoc_of% ha, hb, Category.comp_id]
  · rw [← cancel_epi T.q, reassoc_of% hb, ha, Category.comp_id]

end PositivityTheory.HtPt.Ppic
