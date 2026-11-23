import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPicardGlueFiniteDisjointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionWhiskerLeftRangePreimageSndStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetsInAffineOpenFiniteCoproductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFinAffineOfIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiDisjointOpenCoverFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyOfDisjointOpenPiecesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFamiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDisjointUnionRepresentingFamilyUniqueStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem hasRepAF_of_disjoint_cover {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hcov : ⨆ i, V i = ⊤) (hdisj : Pairwise fun i i' => Disjoint (V i) (V i'))
    (h : ∀ i, HasRepAF A g (Over.mk ((V i).ι ≫ X.hom))) : HasRepAF A g X := by
  choose B b P hP using h
  let Bt : Over S := Over.mk (Sigma.desc fun i => (B i).hom)
  let j : ∀ i, B i ⟶ Bt := fun i => Over.homMk (Sigma.ι (fun i => (B i).left) i) (by simp [Bt])
  have hjl : ∀ i, (j i).left = Sigma.ι (fun i => (B i).left) i := fun i => rfl
  haveI : ∀ i, IsOpenImmersion (j i).left := fun i => by rw [hjl]; infer_instance
  have hjc : ⨆ i, (j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk fun i => (B i).left).surjective x
    rw [sigmaMk_mk]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, y, by rw [hjl]⟩
  have hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange := fun i i' hii' => by
    simp only [hjl]; exact disjoint_opensRange_sigmaι _ i i' hii'
  let bt : Bt ⟶ X := Over.homMk (Sigma.desc fun i => (b i).left ≫ (V i).ι) (by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Bt, Over.mk_hom, colimit.ι_desc_assoc, Cofan.mk_ι_app, Discrete.functor_obj_eq_as, colimit.ι_desc, Category.assoc]
    exact Over.w (b i))
  have hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι := fun i => by
    ext1; simp [j, bt]

  have hk : ∀ i, IsOpenImmersion (A ◁ j i).left := fun i => (GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).1
  have hkc : ⨆ i, (A ◁ j i).left.opensRange = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (snd A Bt).left z ∈ ⨆ i, (j i).left.opensRange := by rw [hjc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    change z ∈ Set.range (A ◁ j i).left
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2]
    exact hi
  have hkd : Pairwise fun i i' => Disjoint (A ◁ j i).left.opensRange (A ◁ j i').left.opensRange := by
    intro i i' hii'
    rw [disjoint_iff, eq_bot_iff]
    rintro z ⟨h1, h2⟩
    change z ∈ Set.range (A ◁ j i).left at h1
    change z ∈ Set.range (A ◁ j i').left at h2
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i)).2] at h1
    rw [(GlobalTheory.T.isOpenImmersion_whiskerLeft_range_preimage_snd A (j i')).2] at h2
    exact (disjoint_iff.1 (hjd hii')).le ⟨h1, h2⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_cechPicard_glue_finite_disjoint_cover (fun i => (A ◁ j i).left) hkc hkd (fun i => cls (P i) (hP i).1.fam.isLB)
  obtain ⟨Pt, hPt, rfl⟩ := cls_surj d
  have hPi : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i) := fun i =>
    (cls_eq_iff (pull_isLB hPt _) (hP i).1.fam.isLB).1 ((cls_pull hPt _ _).trans (hd i))
  refine ⟨Bt, bt, Pt, ⟨GlobalTheory.T.additiveLineBundleFamily_of_disjoint_open_pieces A Bt B j hjc hjd P Pt (fun i => (hP i).1.fam) hPt hPi, fun T t N hN => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx, hxN⟩ := GlobalTheory.T.exists_point_disjointUnion_representingAdditiveFamily A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T t N hN
    refine ⟨x, ⟨hx, hxN⟩, fun y hy => ?_⟩
    refine GlobalTheory.T.point_disjointUnion_representingFamily_unique A X V hcov hdisj Bt B j hjc hjd b bt hb P Pt (fun i => (hP i).1) hPt hPi T y x (hy.1.trans hx.symm) ?_
    rw [Same, ← cls_eq_iff (pull_isLB hPt _) (pull_isLB hPt _), ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hy.2,
      ← (cls_eq_iff hN.isLB (pull_isLB hPt _)).2 hxN]
  · exact GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover V hcov hdisj (fun i => (b i).left) g (fun i => (hP i).2.1)
  · exact GlobalTheory.T.finiteSetsInAffineOpen_finite_coproduct (fun i => (B i).left) (fun i => (hP i).2.2)

theorem hasRepAF_pi : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → ∀ (n : ℕ) (D : Fin n → Type) [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)], (∀ i, HasRepAF A g (Over.mk (spMap (algebraMap R (D i))))) → HasRepAF A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) := by
  intro R _ A _ g _ n D _ _ h
  obtain ⟨V, hcov, hdisj, he⟩ := GlobalTheory.T.spec_pi_disjoint_open_cover_factors R n D
  exact hasRepAF_of_disjoint_cover A g (Over.mk (spMap (algebraMap R (∀ i, D i)))) V hcov hdisj
    (fun i => GlobalTheory.T.hasProperSmoothDualRepresentativeFinAffine_of_iso A g (he i).some.symm (h i))

end GlobalTheory.DualCon.ProdGlue
