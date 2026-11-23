import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbGlue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch

theorem ker_comap_eq_ker_iff {X X' V V' : Scheme.{0}} (m : X' ⟶ X) (v : V ⟶ X) [IsClosedImmersion v]
    (v' : V' ⟶ X') [IsClosedImmersion v'] :
    v.ker.comap m = v'.ker ↔ ∃ w : V' ⟶ V, IsPullback v' w m v := by
  have e : v.ker.subschemeι = inv v.toImage ≫ v := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [comap_eq_ker_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ inv v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso (inv v.toImage)) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]
  · rintro ⟨w, hw⟩
    refine ⟨w ≫ v.toImage, ?_⟩
    refine IsPullback.of_iso hw (Iso.refl _) (Iso.refl _) (asIso v.toImage) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [e]

variable {S Z : Scheme.{0}} (z : Z ⟶ S) (W : S.Opens)

lemma isPullback_restrict {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    IsPullback (pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι) (pullback.snd (z ∣_ W) b) z (b ≫ W.ι) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback (z ∣_ W) b) (isPullback_morphismRestrict z W).flip

def restrictIso {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) : pullback (z ∣_ W) b ≅ pullback z (b ≫ W.ι) :=
  (isPullback_restrict z W b).isoPullback

@[reassoc (attr := simp)]
lemma restrictIso_hom_fst {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.fst z (b ≫ W.ι) = pullback.fst (z ∣_ W) b ≫ (z ⁻¹ᵁ W).ι :=
  (isPullback_restrict z W b).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma restrictIso_hom_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).hom ≫ pullback.snd z (b ≫ W.ι) = pullback.snd (z ∣_ W) b :=
  (isPullback_restrict z W b).isoPullback_hom_snd

@[reassoc (attr := simp)]
lemma restrictIso_inv_snd {Y : Scheme.{0}} (b : Y ⟶ W.toScheme) :
    (restrictIso z W b).inv ≫ pullback.snd (z ∣_ W) b = pullback.snd z (b ≫ W.ι) := by
  rw [Iso.inv_comp_eq, restrictIso_hom_snd]

lemma restrictIso_natural {Y H : Scheme.{0}} (b : Y ⟶ W.toScheme) (h : H ⟶ W.toScheme) (c : Y ⟶ H)
    (hc : c ≫ h = b) (w : c ≫ h ≫ W.ι = b ≫ W.ι) :
    pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp) (by rw [Category.comp_id, hc]) ≫
      (restrictIso z W h).hom = (restrictIso z W b).hom ≫ bc z c (h ≫ W.ι) (b ≫ W.ι) w := by
  apply pullback.hom_ext
  · simp only [bc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_fst_assoc, restrictIso_hom_fst]
  · simp only [bc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc, Category.comp_id,
      restrictIso_hom_snd_assoc, restrictIso_hom_snd]

theorem isHilbRep_restrict_local : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens),
    GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme),
      IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme),
        x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  intro S Z z r W hR
  obtain ⟨H, h, U, u, hprop, hcl, hfin, hflat, hrk, huniv⟩ := hR
  haveI := hcl
  have hv : IsFinFlatRk ((u ≫ (restrictIso z W h).hom) ≫ pullback.snd z (h ≫ W.ι)) r := by
    rw [Category.assoc, restrictIso_hom_snd]
    exact ⟨hfin, hflat, hrk⟩
  set y := mkPt (h ≫ W.ι) (u ≫ (restrictIso z W h).hom) hv with hy
  refine ⟨H, y, h, hprop, rfl, ?_⟩
  intro Y x b hx
  obtain ⟨g, J⟩ := x
  change g = b ≫ W.ι at hx
  subst hx
  set v' := J.1.subschemeι ≫ (restrictIso z W b).inv with hv'
  have e : v' ≫ pullback.snd (z ∣_ W) b = J.1.subschemeι ≫ pullback.snd z (b ≫ W.ι) := by
    rw [hv', Category.assoc, restrictIso_inv_snd]
  have key : ∀ c : Y ⟶ H, HPt.map c y = ⟨b ≫ W.ι, J⟩ ↔ ∃ hf : c ≫ h = b, ∃ w : J.1.subscheme ⟶ U,
      IsPullback v' w (pullback.map (z ∣_ W) b (z ∣_ W) h (𝟙 _) c (𝟙 _) (by simp)
        (by rw [Category.comp_id, hf])) u := by
    intro c
    constructor
    · intro hc
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := congrArg Sigma.fst hc
      have hf : c ≫ h = b := by
        rw [← cancel_mono W.ι, Category.assoc]
        exact h1
      refine ⟨hf, ?_⟩
      rw [HPt.map_eq_mk_iff c y h1] at hc
      have hc' : (u ≫ (restrictIso z W h).hom).ker.comap (bc z c (h ≫ W.ι) (b ≫ W.ι) h1) =
          J.1.subschemeι.ker := hc.trans (Scheme.IdealSheafData.ker_subschemeι _).symm
      obtain ⟨w, hw⟩ := (ker_comap_eq_ker_iff _ _ _).1 hc'
      refine ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b).symm (Iso.refl _) (restrictIso z W h).symm
        ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · simp only [Iso.symm_hom]
        rw [Iso.comp_inv_eq, Category.assoc, restrictIso_natural z W b h c hf h1, Iso.inv_hom_id_assoc]
      · simp
    · rintro ⟨hf, w, hw⟩
      have h1 : c ≫ h ≫ W.ι = b ≫ W.ι := by rw [← Category.assoc, hf]
      rw [HPt.map_eq_mk_iff c y h1]
      refine (?_ : _ = J.1.subschemeι.ker).trans (Scheme.IdealSheafData.ker_subschemeι _)
      refine (ker_comap_eq_ker_iff _ (u ≫ (restrictIso z W h).hom) _).2 ⟨w, ?_⟩
      refine IsPullback.of_iso hw (Iso.refl _) (restrictIso z W b) (Iso.refl _) (restrictIso z W h) ?_ ?_ ?_ ?_
      · simp [hv']
      · simp
      · exact restrictIso_natural z W b h c hf h1
      · simp
  have hJ := J.2
  rw [← e] at hJ
  obtain ⟨f, hfP, huniq⟩ := huniv Y b _ v' inferInstance hJ.1 hJ.2.1 hJ.2.2
  exact ⟨f, (key f).2 hfP, fun c hc => huniq c ((key c).1 hc)⟩

end GlobalTheory.HilbGlue
