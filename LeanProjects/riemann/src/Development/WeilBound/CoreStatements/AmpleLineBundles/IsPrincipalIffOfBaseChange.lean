import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsSecOfFlatPull
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

theorem isAmpleLB_desc {K K' : Type} [Field K] [Field K'] (e : K →+* K') {X X' : Scheme.{0}} (p : X ⟶ Sp K)
    (p' : X' ⟶ Sp K') (φ : X' ⟶ X) (H : IsPullback φ p' p (spMap e)) [IsProper p] (L : LB X) (hL : L.IsLB)
    (h : GlobalTheory.IsAmpleLB (L.pull φ)) : GlobalTheory.IsAmpleLB L := by
  letI := e.toAlgebra
  have hp' : IsProper p' := MorphismProperty.of_isPullback (P := @IsProper) H inferInstance
  have hc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have hs : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hfl : Flat (spMap e) := inferInstance
  have hsu : Surjective (spMap e) := inferInstance
  have hφ : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) H.flip hsu
  refine ⟨hL, hc, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := φ.surjective x
  obtain ⟨n, hn, s', hs', -⟩ := h.exists_affine y
  have hM := GlobalTheory.isLB_lbPow hL n
  have hM' := GlobalTheory.isLB_lbPow h.isLB n
  have hP := LB.isLB_pull hM φ
  have iso := GlobalTheory.lbIso_lbPow_pull hL φ n
  obtain ⟨s₁, e₁⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hP hM' iso.symm s'
  obtain ⟨σ, hσ⟩ := exists_sec_of_flat_pull p p' φ H (fun U W hU hW => hU.inf hW) _ hM s₁ y (e₁.ge hs')
  refine ⟨n, hn, σ, hσ, ?_⟩
  obtain ⟨s₂, e₂⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hM' hP iso (GlobalTheory.secPull σ φ)
  have ha := h.isAffineOpen_nonzeroLocus p' hn s₂
  rw [e₂, GlobalTheory.nonzeroLocus_secPull] at ha
  have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus σ) := ha
  exact GlobalTheory.isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict φ (Out.nonzeroLocus σ)).paste_vert H)

theorem kTriv_desc {S S' : Scheme.{0}} {f : S' ⟶ S} [Flat f] [Surjective f] {A : Over S} {A' : Over S'} [GrpObj A]
    [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  intro R _ t x hx
  let T' : Over S' := Over.mk (pullback.snd t f)
  let u : Over.mk (T'.hom ≫ f) ⟶ Over.mk t := Over.homMk (pullback.fst t f) pullback.condition
  have sq : (pullback.fst t f ≫ x.left) ≫ A.hom = pullback.snd t f ≫ f := by
    rw [Category.assoc, Over.w x]; exact pullback.condition
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
  have e : pushPt h.1.w x' = u ≫ x := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  have m : GlobalTheory.MemKL A' L' x' := GlobalTheory.memKL_of_push h hL hL' hw x' (by rw [e]; exact GlobalTheory.MemKL.comp (A := A) (L := L) (x := x) hx u)
  obtain ⟨z, hz⟩ := (GlobalTheory.memKL_iff_of_kTriv hL' hK x').1 m
  have hx' : x' = 1 := by rw [← hz, toUnit_unique z (toUnit _)]; rfl
  have e₁ : u ≫ x = u ≫ (toUnit _ ≫ η[A]) := by
    rw [← e, hx', ← Category.assoc, comp_toUnit]
    exact map_one (pushHom h T')
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  exact Over.OverMorphism.ext ((cancel_epi (pullback.fst t f)).1 (congrArg (fun q => q.left) e₁))

theorem isPrincipal_iff_of_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  intro E _ _ _ H L L' _ _ e t t' m
  obtain ⟨w, hw, -⟩ := m.lin
  have hfl : Flat (spMap e) := inferInstance
  have hsu : Surjective (spMap e) := inferInstance
  constructor
  · rintro ⟨hp, ha, hk⟩
    have := t.semi.smooth
    have := t.semi.separated
    have : UniversallyClosed t.G.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) m.cart.1.flip ⟨⟨hsu, hfl⟩, inferInstance⟩ inferInstance
    have hp₀ : IsProper t.G.hom := {}
    refine ⟨hp₀, ?_, kTriv_desc m.cart t.PP.isLB t'.PP.isLB ⟨w, hw⟩ hk⟩
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine t.G t.PP.isLB).2
      (isAmpleLB_desc e t.G.hom t'.G.hom m.φ m.cart.1 _ t.PP.isLB ?_)
    exact (GlobalTheory.isAmpleLB_of_relAmple_of_isAffine t'.G t'.PP.isLB ha).of_lbIso (LB.isLB_pull t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩)
  · rintro ⟨hp, ha, hk⟩
    exact ⟨MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hp,
      amplePt _ _ _ _ _ _ m.cart _ _ t.PP.isLB t'.PP.isLB ⟨w, hw⟩ ha hk⟩

end CoverDenseAlt
