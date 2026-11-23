import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.AnForm.R

namespace GlobalTheory.TorRef

theorem effCartier_top' (X : Scheme.{0}) : FinalTheorems.EffCartier (⊤ : X.IdealSheafData) := fun x => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, 1, hx, one_mem _, by simp⟩

theorem effCartier_comap_of_disjoint' {W X : Scheme.{0}} (g : W ⟶ X) (J : X.IdealSheafData)
    (h : ∀ w, g w ∉ J.support) : FinalTheorems.EffCartier (J.comap g) := by
  have : J.comap g = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap, eq_bot_iff]
    exact fun w hw => h w hw
  rw [this]; exact effCartier_top' W

theorem effCartier_comap_of_flat {X Y : Scheme.{0}} (I : X.IdealSheafData) (f : Y ⟶ X) [Flat f]
    (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hI
  rw [← hD]
  exact (D.keepsRegular_iff_effCartier f).1 (D.keepsRegular_of_flat f)

theorem blowup_of_isPullback_of_flat {X X' Y Y' : Scheme.{0}} {π : X' ⟶ X} {g : Y ⟶ X} {π' : Y' ⟶ Y}
    {g' : Y' ⟶ X'} {J : X.IdealSheafData} (hB : FinalTheorems.Blowup π J) (hg : Flat g) (pb : IsPullback g' π' π g) :
    FinalTheorems.Blowup π' (J.comap g) := by
  have hg' : Flat g' := MorphismProperty.of_isPullback pb.flip hg
  refine ⟨?_, fun W h hW => ?_⟩
  · rw [← Scheme.IdealSheafData.comap_comp, ← pb.w, Scheme.IdealSheafData.comap_comp]
    exact effCartier_comap_of_flat _ g' hB.1
  · rw [← Scheme.IdealSheafData.comap_comp] at hW
    obtain ⟨k, hk, hku⟩ := hB.2 W (h ≫ g) hW
    refine ⟨pb.lift k h hk, pb.lift_snd _ _ _, fun m hm => pb.hom_ext ?_ ?_⟩
    · rw [pb.lift_fst]
      exact hku _ (by simp only at hm ⊢; rw [Category.assoc, pb.w, ← Category.assoc, hm])
    · rw [pb.lift_snd]; exact hm

theorem isIso_of_blowup_of_effCartier {X X' : Scheme.{0}} {π : X' ⟶ X} {J : X.IdealSheafData}
    (hB : FinalTheorems.Blowup π J) (hJ : FinalTheorems.EffCartier J) : IsIso π := by
  obtain ⟨s, hs, -⟩ := hB.2 X (𝟙 X) (by rwa [Scheme.IdealSheafData.comap_id])
  obtain ⟨_, -, hu⟩ := hB.2 X' π hB.1
  exact ⟨⟨s, (hu _ (by simp [hs])).trans (hu _ (by simp)).symm, hs⟩⟩

theorem isIso_restrict_of_blowup' {X X' : Scheme.{0}} {π : X' ⟶ X} {J : X.IdealSheafData} (h : FinalTheorems.Blowup π J)
    (U : X.Opens) (hU : ∀ x ∈ U, x ∉ J.support) : IsIso (π ∣_ U) := by
  obtain ⟨σ, hσ, -⟩ := h.2 U U.ι (effCartier_comap_of_disjoint' _ _ fun w => hU _ w.2)
  have pb := isPullback_morphismRestrict π U
  obtain ⟨τ, -, hτ⟩ := h.2 (π ⁻¹ᵁ U) ((π ⁻¹ᵁ U).ι ≫ π)
    (effCartier_comap_of_disjoint' _ _ fun w => hU _ w.2)
  have e : π ∣_ U ≫ σ = (π ⁻¹ᵁ U).ι :=
    (hτ _ (by simp [hσ])).trans (hτ _ rfl).symm
  refine ⟨pb.lift (𝟙 _) σ (by simp [hσ]), pb.hom_ext (by simp) (by simp [e]), by simp⟩

theorem blowBCSt : BlowBCSt :=
  ⟨fun _ _ _ _ _ _ _ _ _ hB hg pb => blowup_of_isPullback_of_flat hB hg pb,
    fun _ _ _ _ hB hJ => isIso_of_blowup_of_effCartier hB hJ,
    fun _ _ _ _ U hB hU => isIso_restrict_of_blowup' hB U fun _ hx hs => Set.disjoint_left.1 hU hx hs⟩

end GlobalTheory.TorRef
