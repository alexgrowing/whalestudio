import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtCharts
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace CanonLB

open TopForm LB
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {R : Type} [CommRing R] {X Y : Scheme.{0}} {f : X ⟶ Sp R} (e : Y ⟶ X) [IsOpenImmersion e]
  {d : ℕ} [SmoothOfRelativeDimension d f]

theorem comp_spMap_id (f : X ⟶ Sp R) : e ≫ f = (e ≫ f) ≫ spMap (RingHom.id R) := by
  simp [spMap]

theorem isFrame_pullForm_openImm {U : X.Opens} {ω : FormsOn f d U} (hω : IsFrame ω)
    {W : Y.Opens} (hW : IsAffineOpen W) (h : W ≤ e ⁻¹ᵁ U) :
    IsFrame (pullForm (comp_spMap_id e f) h ω) := by
  have hle : e ''ᵁ W ≤ U := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact h hy
  have h' : W ≤ e ⁻¹ᵁ (e ''ᵁ W) := (e.preimage_image_eq W).ge
  have hω' : IsFrame (resForm hle ω) := hω.res (hW.image_of_isOpenImmersion e) hle
  have key : pullForm (comp_spMap_id e f) h ω = pullForm (comp_spMap_id e f) h' (resForm hle ω) := by
    rw [pullForm_resForm]
  rw [key]
  have hiso : IsIso (e.appLE (e ''ᵁ W) W h') := by
    have : e.appLE (e ''ᵁ W) W h' = (e.appIso W).hom := by
      rw [Scheme.Hom.appIso_hom, Scheme.Hom.appLE]
      rfl
    rw [this]
    infer_instance
  have sq := appLE_comp_algX (comp_spMap_id e f) h'
  haveI : IsIso (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) := by
    simpa using hiso
  haveI : IsIso (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id]
    infer_instance
  have H : IsPushout (CommRingCat.ofHom (algX f (e ''ᵁ W))) (CommRingCat.ofHom (RingHom.id R))
      (CommRingCat.ofHom (e.appLE (e ''ᵁ W) W h').hom) (CommRingCat.ofHom (algX (e ≫ f) W)) := by
    refine IsPushout.of_vert_isIso ⟨?_⟩
    ext x
    exact RingHom.congr_fun sq x
  exact ⟨hW, hω'.gen.formMapSq (RingHom.id R) (e.appLE (e ''ᵁ W) W h').hom sq H⟩

abbrev OIdx (e : Y ⟶ X) (K : CanonLB f d) : Type :=
  Σ i : K.bundle.ι, {W : Y.Opens // IsAffineOpen W ∧ W ≤ e ⁻¹ᵁ K.bundle.U i}

def oBundle (e : Y ⟶ X) (K : CanonLB f d) : LB Y :=
  ZH.UFib.refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1) (fun a => a.2.2.2)

theorem resG_oBundle_g (K : CanonLB f d) (a b : OIdx e K)
    {W : Y.Opens} (h : W ≤ (oBundle e K).U a ⊓ (oBundle e K).U b) :
    resG Y h ((oBundle e K).g a b : Γ(Y, (oBundle e K).U a ⊓ (oBundle e K).U b)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W
        (h.trans (fun _ hy => ⟨a.2.2.2 hy.1, b.2.2.2 hy.2⟩))).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) := by
  simp only [oBundle, ZH.UFib.refinePull, res, pullU, Units.coe_map, MonoidHom.coe_coe]
  erw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  simp only [Scheme.Hom.appLE, Category.assoc, resG]
  rw [← Functor.map_comp]
  rfl

theorem iSup_oIdx (K : CanonLB f d) : ⨆ a : OIdx e K, a.2.1 = ⊤ :=
  eq_top_iff.2 fun y _ => by
    obtain ⟨i, hi⟩ := exists_chart K.isLB (e y)
    obtain ⟨W, hW, hy, hsub⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := e ⁻¹ᵁ K.bundle.U i) hi
    exact Opens.mem_iSup.2 ⟨⟨i, W, hW, fun z hz => hsub hz⟩, hy⟩

def oChartPull (K : CanonLB f d) : ChartPull (oBundle e K) K.bundle e where
  idx a := a.1
  le a := a.2.2.2
  g y a b h h' := ZH.UFib.gm_refinePull K.bundle e (fun a : OIdx e K => a.2.1) (fun a => a.1)
    (fun a => a.2.2.2) y a b h h'

variable [SmoothOfRelativeDimension d (e ≫ f)]

theorem resForm_pullForm_om (K : CanonLB f d) (a b : OIdx e K) {W : Y.Opens} (hW : IsAffineOpen W)
    (ha : W ≤ a.2.1) (hb : W ≤ b.2.1) (h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1)) :
    resForm hb (pullForm (comp_spMap_id e f) b.2.2.2 (K.om b.1)) =
      (e.appLE (K.bundle.U a.1 ⊓ K.bundle.U b.1) W h).hom
          ((K.bundle.g a.1 b.1 : Γ(X, K.bundle.U a.1 ⊓ K.bundle.U b.1))) •
        resForm ha (pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)) := by
  have hfa := isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2
  have h₁ := (K.isFrame a.1).coeff_pullForm (comp_spMap_id e f) a.2.2.2 hfa inf_le_left ha h
    (resForm inf_le_right (K.om b.1))
  rw [pullForm_resForm] at h₁
  rw [g_eq_ratio, resForm_pullForm]
  exact (hfa.coeff_smul_resForm hW ha _).symm.trans (congrArg (· • _) h₁)

def openImm (K : CanonLB f d) : CanonLB (e ≫ f) d where
  bundle := oBundle e K
  isLB := ZH.UFib.refinePull_isLB K.bundle K.isLB e _ _ _ (iSup_oIdx e K)
  affine a := a.2.2.1
  om a := pullForm (comp_spMap_id e f) a.2.2.2 (K.om a.1)
  gen a := (isFrame_pullForm_openImm e (K.isFrame a.1) a.2.2.1 a.2.2.2).gen
  trans a b W hW ha hb := by
    have h : W ≤ e ⁻¹ᵁ (K.bundle.U a.1 ⊓ K.bundle.U b.1) :=
      le_inf (ha.trans a.2.2.2) (hb.trans b.2.2.2)
    exact (resForm_pullForm_om e K a b hW ha hb h).trans
      (congrArg (· • _) (resG_oBundle_g e K a b (le_inf ha hb)).symm)

end CanonLB

theorem cls_canonLB_openImmersion : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : X ⟶ Sp R)
    (e : Y ⟶ X) [IsOpenImmersion e] (d : ℕ) [SmoothOfRelativeDimension d f]
    [SmoothOfRelativeDimension d (e ≫ f)] (K : CanonLB f d) (K' : CanonLB (e ≫ f) d),
    cls K'.bundle K'.isLB = CechPic.pull e (cls K.bundle K.isLB) := by
  intro R _ X Y f e _ d _ _ K K'
  have hp : (K.bundle.pull e).IsLB := Semi.LB.isLB_linComb K.isLB _ _
  calc cls K'.bundle K'.isLB = cls (K.openImm e).bundle (K.openImm e).isLB :=
        (cls_eq_iff _ _).2 (K'.lbIso (K.openImm e))
    _ = cls (K.bundle.pull e) hp :=
        (cls_eq_iff _ _).2 (LBIso.chartPull (K.oChartPull e)
          (Geo.Tor.chartPullPull K.bundle e e rfl) (K.lbIso K))
    _ = CechPic.pull e (cls K.bundle K.isLB) := cls_pull K.isLB e hp

end GlobalTheory
