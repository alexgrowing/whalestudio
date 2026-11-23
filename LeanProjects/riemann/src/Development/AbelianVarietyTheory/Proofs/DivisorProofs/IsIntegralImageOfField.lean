import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfIsSchemeTheoreticallyDominantOfFractionRing

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem isIntegral_image_of_field {K : Type} [Field K] {S : Scheme.{0}} (g : Sp K ⟶ S) : IsIntegral g.image := by
  have : QuasiCompact g := inferInstance
  have := GlobalTheory.isSchemeTheoreticallyDominant_toImage g
  have : IsReduced g.image := IsSchemeTheoreticallyDominant.isReduced g.toImage
  have hi : IsIrreducible (Set.range g.toImage) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ g.toImage.continuous.continuousOn
  have hc := hi.closure
  rw [g.toImage.denseRange.closure_range] at hc
  have : IrreducibleSpace g.image := { isPreirreducible_univ := hc.2, toNonempty := ⟨hc.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem lbIso_factor {X Y Z : Scheme.{0}} {L : LB X} {L' : LB Y} {M : LB Z} (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB)
    {F : Y ⟶ X} {a' : Z ⟶ Y} {a : Z ⟶ X} (e : a' ≫ F = a) (h' : LBIso L' (L.pull F)) (h : LBIso M (L.pull a)) :
    LBIso M (L'.pull a') :=
  LBIso.trans hM (pull_isLB hL _) (pull_isLB hL' _) h
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L' a' a' rfl) (chartPullSame L (fun _ => a) (fun _ => F) _ a' fun _ => e.symm) h').symm

theorem exists_grpPullback_factor {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G'' : Over S''} [GrpObj G'']
    (f : S' ⟶ S) (g : S'' ⟶ S') {F : G''.left ⟶ G.left} (h : IsGrpPullback G'' G (g ≫ f) F) :
    ∃ F' : G''.left ⟶ ((Over.pullback f).obj G).left, F' ≫ pullback.fst G.hom f = F ∧
      IsGrpPullback G'' ((Over.pullback f).obj G) g F' := by
  have hF : pullback.lift F (G''.hom ≫ g) (by rw [h.1.w, Category.assoc]) ≫ pullback.fst G.hom f = F :=
    pullback.lift_fst _ _ _
  exact ⟨_, hF, (isGrpPullback_pullback G f).cancel (h.congr rfl hF.symm) (pullback.lift_snd _ _ _)⟩

theorem PreCover.nonempty_labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)), PreCover D → Nonempty (LabCover D) := by
  intro R _ _ _ D C
  have := C.proper
  have : QuasiCompact C.gp := inferInstance
  obtain ⟨P', w, hP⟩ := GlobalTheory.UU.exists_pull C.P (GlobalTheory.UU.toBase_mul_pullback C.G C.gp.imageι)
  obtain ⟨α', hα, hα'⟩ := exists_grpPullback_factor C.gp.imageι C.gp.toImage
    (C.α_cart.congr C.gp.toImage_imageι.symm rfl)
  refine ⟨{ S := C.gp.image
            π := C.gp.imageι ≫ C.π
            proper := inferInstance
            integral := isIntegral_image_of_field C.gp
            gp := C.gp.toImage
            gp_π := by rw [C.gp.toImage_imageι_assoc, C.gp_π]
            dominant := inferInstance
            G := (Over.pullback C.gp.imageι).obj C.G
            semi := IsSemiAbelian.pullback _ _ C.semi
            P := P'
            A := C.A
            α := α'
            α_cart := hα'
            α_lb := lbIso_factor C.P.L.isLB P'.L.isLB C.A.isLB hα ⟨w, hP.gen⟩ C.α_lb
            n := C.n
            n_prime := C.n_prime
            n_odd := C.n_odd
            n_unit := C.n_unit
            lab := C.lab
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', i₁, i₂, i₃, io, G', j₁, j₂, β, D', A', U', hD, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    C.trait W hW φ (ξ ≫ C.gp.imageι) hφ hloc (by rw [Category.assoc, hξ])
  obtain ⟨β', hβ, hβ'⟩ := exists_grpPullback_factor C.gp.imageι (spMap io ≫ ξ)
    (h₄.congr (Category.assoc _ _ _).symm rfl)
  refine ⟨W', i₁, i₂, i₃, io, G', j₁, j₂, β', D', A', U', hD, h₁, h₂, h₃, hβ',
    lbIso_factor C.P.L.isLB P'.L.isLB U'.LG.isLB hβ ⟨w, hP.gen⟩ h₅, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' a b c d
  refine h₆ F em hF j p p₁ p' x' a b c ?_
  have := congrArg (· ≫ pullback.fst C.G.hom C.gp.imageι) d
  simp only [Category.assoc] at this
  rw [← hα, ← hβ]
  exact this

end GlobalTheory.Mum
