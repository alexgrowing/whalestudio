import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

inductive IsSmoothBlowupSeq {S Y : Scheme.{0}} (f : Y ⟶ S) (B : Set Y) : ∀ {Y' : Scheme.{0}}, (Y' ⟶ Y) → Prop

  | id : IsSmoothBlowupSeq f B (𝟙 Y)

  | step {Y₁ Y₂ : Scheme.{0}} {s : Y₁ ⟶ Y} (J : Y₁.IdealSheafData) (π : Y₂ ⟶ Y₁) :
      IsSmoothBlowupSeq f B s → Smooth (J.subschemeι ≫ s ≫ f) → (J.support : Set Y₁) ⊆ s ⁻¹' B →
      FinalTheorems.Blowup π J → IsSmoothBlowupSeq f B (π ≫ s)

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.IsSmoothBlowupSeq.mono {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B B' : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (hB : B ⊆ B') : _root_.GlobalTheory.IsSmoothBlowupSeq f B' s := by
  induction h with
  | id => exact .id
  | step J π _ hsm hsupp hbl ih =>
    exact .step J π ih hsm (hsupp.trans (Set.preimage_mono hB)) hbl

theorem IsSmoothBlowupSeq.single {S Y Y' : Scheme.{0}} {f : Y ⟶ S} {B : Set Y} (J : Y.IdealSheafData) (π : Y' ⟶ Y)
    (h₁ : Smooth (J.subschemeι ≫ f)) (h₂ : (J.support : Set Y) ⊆ B) (h₃ : FinalTheorems.Blowup π J) :
    IsSmoothBlowupSeq f B π := by
  simpa using IsSmoothBlowupSeq.step (f := f) (B := B) J π .id (by simpa using h₁) (by simpa using h₂) h₃

namespace Principalise

theorem effCartier_top (X : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : X.IdealSheafData) := fun x => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap g) := by
  have htop : J.comap g = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
    ext w
    simpa using h w
  intro w
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  refine ⟨⟨V, hV⟩, 1, hwV, one_mem _, ?_⟩
  rw [htop, Ideal.span_singleton_one]
  simp [Scheme.IdealSheafData.ideal_top]

theorem blowup_id {X : Scheme.{0}} {J : X.IdealSheafData} (h : FinalTheorems.EffCartier J) : FinalTheorems.Blowup (𝟙 X) J :=
  ⟨by rwa [Scheme.IdealSheafData.comap_id], fun _ g _ => ⟨g, Category.comp_id g, fun _ e => by simpa using e⟩⟩

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup {X X' : Scheme.{0}} {π : X' ⟶ X}
    {J : X.IdealSheafData} (h : _root_.ReciprocityTheory.AnForm.R.FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : ∀ x ∈ U, x ∉ J.support) : IsIso (π ∣_ U) := by
  have hcart : ∀ (W : Scheme.{0}) (k : W ⟶ U.toScheme), _root_.ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap (k ≫ U.ι)) := by
    intro W k
    refine _root_.GlobalTheory.Principalise.effCartier_comap_of_disjoint _ J fun w => hU _ ?_
    rw [Scheme.Hom.comp_apply]
    have hmem : U.ι (k w) ∈ Set.range U.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem
  have hσ' := hcart U.toScheme (𝟙 _)
  rw [Category.id_comp] at hσ'
  obtain ⟨σ, hσ, -⟩ := h.2 U.toScheme U.ι hσ'
  have hsnd : IsIso (pullback.snd π U.ι) := by
    refine ⟨⟨pullback.lift σ (𝟙 _) (by rw [hσ, Category.id_comp]), ?_,
      pullback.lift_snd _ _ _⟩⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      have hg := hcart _ (pullback.snd π U.ι)
      rw [← pullback.condition] at hg
      exact (h.2 _ _ hg).unique (by rw [Category.assoc, hσ, pullback.condition]) rfl
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  rw [morphismRestrict]
  infer_instance

end Principalise

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.IsSmoothBlowupSeq.isIso_restrict {S Y Y' : Scheme.{0}} {f : Y ⟶ S}
    {B : Set Y} {s : Y' ⟶ Y}
    (h : _root_.GlobalTheory.IsSmoothBlowupSeq f B s) (U : Y.Opens) (hU : ∀ y ∈ U, y ∉ B) : IsIso (s ∣_ U) := by
  induction h with
  | id => infer_instance
  | @step Y₁ Y₂ s J π hs hsm hsupp hbl ih =>
    rw [morphismRestrict_comp]
    have : IsIso (π ∣_ s ⁻¹ᵁ U) :=
      _root_.GlobalTheory.Principalise.isIso_restrict_of_blowup hbl _ fun x hx hxJ => hU _ hx (hsupp hxJ)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ this ih

namespace Principalise

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace in

theorem _root_.GlobalTheory.Principalise.nonempty_compl_support {Y : Scheme.{0}} [IsIntegral Y] {I : Y.IdealSheafData} (hI : I ≠ ⊥) :
    (I.support.compl : Set Y).Nonempty := by
  by_contra hne
  apply hI
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  ext x
  simp only [Set.not_nonempty_iff_eq_empty] at hne
  have : x ∉ (I.support.compl : Set Y) := by simp [hne]
  simpa using this

end Principalise

namespace Published

def Principalisation : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (d : ℕ) (Y : Scheme.{0}) (f : Y ⟶ Sp k),
    IsIntegral Y → SmoothOfRelativeDimension d f → IsProjOver f →
    ∀ I : Y.IdealSheafData, I ≠ ⊥ →
      ∃ (Y' : Scheme.{0}) (s : Y' ⟶ Y),
        IsIntegral Y' ∧ SmoothOfRelativeDimension d (s ≫ f) ∧ IsProjOver (s ≫ f) ∧
        IsSmoothBlowupSeq f (I.support : Set Y) s ∧ IsIso (s ∣_ I.support.compl) ∧
        FinalTheorems.EffCartier (I.comap s) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (I.comap s).support)

end Published

end GlobalTheory
