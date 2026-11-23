import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.SplitTorusExtension

theorem one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    change ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h₁ : (e * e).left = e.left := by
    rw [h.2 T 1 1 e e rfl rfl, _root_.mul_one]
    rfl
  have h₂ : e * e = e := Over.OverMorphism.ext h₁
  have h₃ : e = 1 := by simpa using h₂
  rw [← h₃]
  rfl

theorem eq_one {S S' : Scheme.{0}} {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {G H : Over S} [GrpObj G] [GrpObj H]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G f φ)
    (hψ : IsGrpPullback H' H f ψ) (i : G' ⟶ H') [IsMonHom i] [Mono i] (u : G ⟶ H)
    (hu : i.left ≫ ψ = φ ≫ u.left) (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ G) (ht : t ≫ u = 1) : t = 1 := by
  have hw : t.left ≫ G.hom = T.hom ≫ f := Over.w t
  let s : T.left ⟶ G'.left := hφ.1.lift t.left T.hom hw
  have hs : s ≫ φ = t.left := hφ.1.lift_fst _ _ _
  let s' : T ⟶ G' := Over.homMk s (hφ.1.lift_snd _ _ _)
  have h1 : s' ≫ i = 1 := by
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [← one_left hψ T, Over.comp_left, Category.assoc, hu, ← Category.assoc]
      change (s ≫ φ) ≫ u.left = _
      rw [hs, ← Over.comp_left, ht]
    · rw [Over.w, Over.w]
  have h2 : s' = 1 := by
    have h3 : (1 : T ⟶ G') ≫ i = 1 := by simp [Hom.one_def]
    rw [← h3] at h1
    exact (cancel_mono i).mp h1
  apply Over.OverMorphism.ext
  rw [one_left hφ T, ← h2]
  exact hs.symm

end PositivityTheory.Xgn.SplitTorusExtension

theorem PositivityTheory.Xgn.exists_split_torus_extension : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z' : Scheme.{0}) [IsIntegral Z'] [AlgebraicGeometry.IsNoetherian Z'], IsNormalScheme Z' → ∀ (G : Over Z') [GrpObj G], IsSemiAbelian G → ∀ (L' : Type) [Field L'] (j : Sp L' ⟶ Z'), GlobalTheory.IsGenericPointHom j → ∀ τ : TorusExtension ((Over.pullback j).obj G), letI := τ.addCommGroup; ∃ u : splitTorus Z' τ.X ⟶ G, IsMonHom u ∧ ∀ (A : Type) [CommRing A] (g : L' →+* A) (t : Over.mk (spMap g ≫ j) ⟶ splitTorus Z' τ.X), t ≫ u = 1 → t = 1 := by
  intro hext Z' _ _ hnorm G _ hG L' _ j hj τ
  letI := τ.addCommGroup
  haveI := τ.free
  haveI := τ.finite
  haveI := τ.i_hom
  haveI : Mono τ.i := τ.isKernel.mono_fst_of_mono
  have hT : IsSemiAbelian (splitTorus Z' τ.X) :=
    ((GlobalTheory.splitTorus_properties Z').1 τ.X).2.2.2.2.2.2.2.2.1
  obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange Z' (Sp L') j τ.X
  haveI := he
  have hφ : IsGrpPullback (splitTorus (Sp L') τ.X) (splitTorus Z' τ.X) j
      (e.hom.left ≫ pullback.fst (splitTorus Z' τ.X).hom j) := by
    have h0 := (isGrpPullback_of_iso e).comp (isGrpPullback_pullback (splitTorus Z' τ.X) j)
    rwa [Category.id_comp] at h0
  have hψ := isGrpPullback_pullback G j
  obtain ⟨F, ⟨hF, hu⟩, -⟩ :=
    GlobalTheory.Published.SemiAbelianHomExtension.generic_of_isGrpPullback hext hnorm hj hT hG hφ hψ τ.i
  refine ⟨F, hF, fun A _ g t ht => ?_⟩
  haveI := hF
  exact SplitTorusExtension.eq_one hφ hψ τ.i F hu (Over.mk (spMap g)) t ht
