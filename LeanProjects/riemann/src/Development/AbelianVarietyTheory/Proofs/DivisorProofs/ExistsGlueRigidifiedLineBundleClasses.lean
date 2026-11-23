import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineBundlePullOfIsLineBundleOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLineBundleIsoOnOpenOfRestrictionIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetractStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedLineBundleIsoCocycleIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycleStatement

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_glue_rigidified (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X) (hep : e ≫ p = 𝟙 Y) (hp : FnBij p)
    (Ix : Type) (X' : Ix → Scheme.{0}) (f : ∀ i, X' i ⟶ X) (V : Ix → Y.Opens) (c : ∀ i, Pic (X' i))
    (hf : ∀ i, IsOpenImmersion (f i)) (hr : ∀ i x, x ∈ Set.range (f i) ↔ p x ∈ V i) (hV : ∀ y, ∃ i, y ∈ V i)
    (hrig : ∀ (i : Ix) (T : Scheme.{0}) (t : T ⟶ X' i) (s : T ⟶ Y), t ≫ f i = s ≫ e → GlobalTheory.CechPic.pull t (c i) = 0)
    (hov : ∀ (i k : Ix) (T : Scheme.{0}) (a : T ⟶ X' i) (b : T ⟶ X' k), a ≫ f i = b ≫ f k →
      GlobalTheory.CechPic.pull a (c i) = GlobalTheory.CechPic.pull b (c k)) :
    ∃ c₀ : Pic X, GlobalTheory.CechPic.pull e c₀ = 0 ∧ ∀ i, GlobalTheory.CechPic.pull (f i) c₀ = c i := by
  have hpe : ∀ y : Y, p (e y) = y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hep]; rfl
  have hrange : ∀ i, (f i).opensRange = p ⁻¹ᵁ V i := fun i ↦ by
    ext x; exact hr i x
  choose M hM hMc using fun i ↦ cls_surj (c i)
  choose L hL hLM using fun i ↦ GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion X (X' i) (f i) (M i) (hM i)
  have hL' : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i) := fun i ↦ hrange i ▸ hL i
  have hfm : ∀ i (z : X' i), f i z ∈ p ⁻¹ᵁ V i := fun i z ↦ (hr i _).1 ⟨z, rfl⟩
  have hfl : ∀ i, ((L i).pull (f i)).IsLB := fun i ↦ GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) (f i) (hL' i) (hfm i)
  have hcl : ∀ i, cls _ (hfl i) = c i := fun i ↦ ((cls_eq_iff (hfl i) (hM i)).2 (hLM i)).trans (hMc i)
  have lifts : ∀ i (T : Scheme.{0}) (g : T ⟶ X), (∀ z, g z ∈ p ⁻¹ᵁ V i) → ∃ t : T ⟶ X' i, t ≫ f i = g :=
    fun i T g hg ↦ ⟨IsOpenImmersion.lift (f i) g (by rintro _ ⟨z, rfl⟩; exact (hr i _).2 (hg z)),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hpl : ∀ i (T : Scheme.{0}) (t : T ⟶ X' i) (g : T ⟶ X), t ≫ f i = g →
      ∃ h : ((L i).pull g).IsLB, cls _ h = GlobalTheory.CechPic.pull t (c i) := by
    rintro i T t _ rfl
    have h : ((L i).pull (t ≫ f i)).IsLB := GlobalTheory.T.isLineBundle_pull_of_isLineBundleOnOpen X _ _ (L i) _ (hL' i) fun z ↦ by
      rw [Scheme.Hom.comp_apply]; exact hfm i _
    refine ⟨h, ?_⟩
    rw [← hcl i, ← cls_pull (hfl i) t (pull_isLB (hfl i) t)]
    exact ((cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleOnOpen_pull_comp_iso X _ _ _ (L i) (f i) t (hL' i) (hfm i))).symm
  have hR : ∀ i, ∃ r : RigD e (L i), RigOn e (L i) r := fun i ↦ by
    refine GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open X Y e (V i) (L i) (fun a y hy ↦ ?_) ?_
    · have : p (e y) ∈ V i := (hL' i).le a hy
      rwa [hpe] at this
    · obtain ⟨t, ht⟩ := lifts i _ ((V i).ι ≫ e) fun z ↦ by
        rw [Scheme.Hom.comp_apply]
        change p (e _) ∈ V i
        rw [hpe]
        exact z.2
      obtain ⟨h, hc⟩ := hpl i _ t _ ht
      exact (cls_eq_zero_iff h).1 (hc.trans (hrig i _ t _ ht))
  choose r hr' using hR
  have hw : ∀ i k, ∃ w : Cmp (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k), IsoOn (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w ∧
      Norm e (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k) w (r i) (r k) := fun i k ↦ by
    obtain ⟨a, ha⟩ := lifts i _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.1
    obtain ⟨b, hb⟩ := lifts k _ (p ⁻¹ᵁ (V i ⊓ V k)).ι fun z ↦ z.2.2
    obtain ⟨h1, e1⟩ := hpl i _ a _ ha
    obtain ⟨h2, e2⟩ := hpl k _ b _ hb
    obtain ⟨w, hw⟩ := GlobalTheory.T.exists_isLineBundleIsoOnOpen_of_restriction_iso X (p ⁻¹ᵁ (V i ⊓ V k)) (L i) (L k)
      ((cls_eq_iff h1 h2).1 (e1.trans ((hov i k _ a b (ha.trans hb.symm)).trans e2.symm)))
    exact GlobalTheory.T.exists_lineBundleIso_normalisedAlongSection_retraction X Y p e hep (V i ⊓ V k) _ _ (L i) (L k) w (r i) (r k) (hL' i) (hL' k)
      (fun _ h ↦ h.1) (fun _ h ↦ h.2) hw (hr' i) (hr' k)
  choose w hwi hwn using hw
  obtain ⟨N, hN, hv⟩ := GlobalTheory.T.lineBundle_glue_of_openCover_cocycle X Ix (fun i ↦ p ⁻¹ᵁ V i) L w (fun x ↦ hV (p x)) hL' hwi
    fun i j k x a b d ha hb hd ↦ GlobalTheory.T.normalised_lineBundleIso_cocycle_identity X Y p e hep hp (V i ⊓ V j ⊓ V k) _ _ _ _ _ _ (L i) (L j) (L k)
      (w i j) (w j k) (w i k) (r i) (r j) (r k) (hL' i) (hL' j) (hL' k) (fun _ h ↦ h)
      (fun _ h ↦ ⟨⟨h.1, h.1.2, h.2⟩, h.1.1, h.2⟩) (hwi i j) (hwi j k) (hwi i k) (hwn i j) (hwn j k) (hwn i k)
      x a b d ⟨⟨(hL' i).le a ha, (hL' j).le b hb⟩, (hL' k).le d hd⟩ ha hb hd
  have hNc : ∀ i, GlobalTheory.CechPic.pull (f i) (cls N hN) = c i := fun i ↦ by
    obtain ⟨v, hv⟩ := hv i
    rw [← hcl i, ← cls_pull hN (f i) (pull_isLB hN _)]
    exact (cls_eq_iff _ _).2 (GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen X _ _ N (L i) v (f i) hv (hfm i))
  refine ⟨cls N hN - GlobalTheory.CechPic.pull p (GlobalTheory.CechPic.pull e (cls N hN)), ?_, fun i ↦ ?_⟩
  · rw [map_sub, ← pull_comp e p, hep, pull_id, sub_self]
  · obtain ⟨t, ht⟩ := lifts i _ ((f i ≫ p) ≫ e) fun z ↦ by
      rw [Scheme.Hom.comp_apply]
      change p (e _) ∈ V i
      rw [hpe, Scheme.Hom.comp_apply]
      exact hfm i z
    rw [map_sub, hNc, ← pull_comp (f i) p, ← pull_comp (f i ≫ p) e, ← ht, pull_comp, hNc,
      hrig i _ t _ ht, sub_zero]

end GlobalTheory.PicGlue
