import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrincipalObjectDescendsLargeSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackCompSpreadToSubringStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpreadStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelSectionsSpreadToSubringStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegSpreadCore

theorem spMap_subtype_eq {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) :
    spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem spMap_inclusion_eq {S : Type} [CommRing S] {R₀ R₁ R₂ : Subring S} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) (h : R₀ ≤ R₂) :
    spMap (Subring.inclusion h) = spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem siegPB_spread_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ sE e hd hu
  classical
  obtain ⟨φd, φd₂, hφd, hsd, hwd, hld⟩ := hd
  obtain ⟨φu, φu₂, hφu, hsu, hwu, hlu⟩ := hu
  haveI := d₀.ab.smooth; haveI := d₀.ab.proper; haveI := u.ab.smooth; haveI := u.ab.proper
  have hZ : IsPullback (pullback.lift φu (e.A.hom ≫ spMap R₀.subtype) (by rw [hφu.1.w, Category.assoc]))
      e.A.hom (pullback.snd u.A.hom h₀) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u.A.hom h₀)
    rw [pullback.lift_fst]; exact hφu.1
  obtain ⟨F₁, hF₁⟩ := GlobalTheory.T.baseChange_iso_spreads_to_subring S R₀ e.A.left d₀.A.left (pullback u.A.hom h₀) e.A.hom d₀.A.hom
    (pullback.snd u.A.hom h₀) φd _ hφd.1 hZ
  let R' : Subring S := Subring.closure ((R₀ : Set S) ∪ (F₁ : Set S))
  have hR0 : R₀ ≤ R' := fun x hx => Subring.subset_closure (Or.inl hx)
  have hF1 : (F₁ : Set S) ⊆ R' := fun x hx => Subring.subset_closure (Or.inr hx)
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R₀) (Sp R') s₀
    (spMap (Subring.inclusion hR0) ≫ s₀) (spMap (Subring.inclusion hR0)) d₀ rfl
  have hd'c := hd'
  obtain ⟨φ', φ'₂, hφ', hs', hw', hl'⟩ := hd'
  have eR' := spMap_subtype_eq hR0
  let j : e.A.left ⟶ d'.A.left := hφ'.1.lift φd (e.A.hom ≫ spMap R'.subtype)
    (by rw [hφd.1.w, eR', Category.assoc])
  have hj1 : j ≫ φ' = φd := hφ'.1.lift_fst _ _ _
  have hj2 : j ≫ d'.A.hom = e.A.hom ≫ spMap R'.subtype := hφ'.1.lift_snd _ _ _
  obtain ⟨ψZ, hψZ1, hψZ2⟩ := hF₁ R' hR0 hF1 d'.A.left d'.A.hom φ' j hφ'.1 hj1 hj2
  let ψ := ψZ ≫ pullback.fst u.A.hom h₀
  have hψ : IsPullback ψ d'.A.hom u.A.hom (spMap (Subring.inclusion hR0) ≫ h₀) :=
    hψZ2.paste_horiz (IsPullback.of_hasPullback _ _)
  have hjψ : j ≫ ψ = φu := by
    show j ≫ ψZ ≫ pullback.fst u.A.hom h₀ = φu
    rw [reassoc_of% hψZ1, pullback.lift_fst]
  have eh : spMap R'.subtype ≫ spMap (Subring.inclusion hR0) ≫ h₀ = spMap R₀.subtype ≫ h₀ := by
    rw [← Category.assoc, ← eR']
  have gj : IsGrpPullback e.A d'.A (spMap R'.subtype) j :=
    IsGrpPullback.cancel hφ' (by rw [hj1, ← eR']; exact hφd) hj2
  obtain ⟨j₂, hsj⟩ := GlobalTheory.SiegDesc.exists_isSquare hj2
  have hj₂ : j₂ ≫ φ'₂ = φd₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst d₀.A d₀.A).left = _ ≫ (fst d₀.A d₀.A).left
      rw [Category.assoc, hs'.1, ← Category.assoc, hsj.1, Category.assoc, hj1, hsd.1]
    · show (_ ≫ _) ≫ (snd d₀.A d₀.A).left = _ ≫ (snd d₀.A d₀.A).left
      rw [Category.assoc, hs'.2, ← Category.assoc, hsj.2, Category.assoc, hj1, hsd.2]
  have hwj : LBIso e.P (d'.P.pull j₂) := by
    rw [← hj₂] at hwd
    exact (hwd.trans e.isLB (pull_isLB d₀.isLB _) (pull_isLB (pull_isLB d₀.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull d₀.isLB φ'₂ j₂).symm).trans e.isLB
      (pull_isLB (pull_isLB d₀.isLB _) _) (pull_isLB d'.isLB _) (GlobalTheory.SiegelPullComp.iso_pull j₂ hw').symm
  have hlj : ∀ a, (e.lev a).left ≫ j = spMap R'.subtype ≫ (d'.lev a).left := by
    intro a
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hj1, hld a, Category.assoc, hl' a, ← Category.assoc, ← eR']
    · have a₁ : (e.lev a).left ≫ e.A.hom = 𝟙 _ := Over.w (e.lev a)
      have a₂ : (d'.lev a).left ≫ d'.A.hom = 𝟙 _ := Over.w (d'.lev a)
      rw [Category.assoc, hj2, reassoc_of% a₁, Category.assoc, a₂]
      simp
  obtain ⟨F₂, hF₂⟩ := GlobalTheory.T.exists_finset_isGrpPullback_comp_of_subring_le g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ gj (by rw [eh, hjψ]; exact hφu)
  obtain ⟨F₃, hF₃⟩ := GlobalTheory.T.lbIso_spread_alt g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ j₂ φu₂ gj.1 hsj hwj
    (by rw [hjψ]; exact hsu) hwu
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.T.siegel_level_sections_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ hlj
    (fun a => by rw [eh, hjψ]; exact hlu a)
  refine ⟨F₁ ∪ F₂ ∪ F₃ ∪ F₄, fun R₁ hle hF s₁ d₁ hd₁ => ?_⟩
  have hsub : ∀ G : Finset S, G ⊆ F₁ ∪ F₂ ∪ F₃ ∪ F₄ → (G : Set S) ⊆ R₁ :=
    fun G h => (Finset.coe_subset.2 h).trans hF
  have hR'1 : R' ≤ R₁ := Subring.closure_le.2 (Set.union_subset hle
    (hsub F₁ (by intro x; simp only [Finset.mem_union]; tauto)))
  have eR1 := spMap_inclusion_eq hR0 hR'1 hle
  have hd₁' : SiegPB d₁ d' (spMap (Subring.inclusion hR'1)) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd'c (by rw [← eR1]; exact hd₁)
  obtain ⟨φ₁, φ₁₂, hφ₁, hs₁, hw₁, hl₁⟩ := hd₁'
  have gm := hF₂ R₁ hR'1 (hsub F₂ (by intro x; simp only [Finset.mem_union]; tauto)) d₁.A φ₁ hφ₁
  have e2 : spMap (Subring.inclusion hR'1) ≫ spMap (Subring.inclusion hR0) ≫ h₀ =
      spMap (Subring.inclusion hle) ≫ h₀ := by rw [eR1, Category.assoc]
  rw [e2] at gm
  obtain ⟨χ₂, hχ⟩ := GlobalTheory.SiegDesc.exists_isSquare gm.1.w
  refine ⟨φ₁ ≫ ψ, χ₂, gm, hχ, hF₃ R₁ hR'1 (hsub F₃ (by intro x; simp only [Finset.mem_union]; tauto))
    s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁.1 hs₁ hw₁ hχ, fun a => ?_⟩
  have := hF₄ R₁ hR'1 (hsub F₄ (by intro x; simp only [Finset.mem_union]; tauto)) s₁ d₁ φ₁
    (by rw [e2]; exact gm) hl₁ a
  rw [e2] at this
  exact this

end GlobalTheory.SiegSpreadCore
