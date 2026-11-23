import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearClosedImmersionProjectiveSpaceCodimTStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerNeBotAndNotEffCartierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoNearOrCentreMeetsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenIntegralOfSmoothOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftOfReducedOfSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictOfClosedImmersionNearGenericStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIntegralKrullDimEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrictStatement

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.WeakRes

theorem isProjOver_comp_closed {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) [IsClosedImmersion g]
    {f : X ⟶ Sp R} (hf : IsProjOver f) : IsProjOver (g ≫ f) := by
  obtain ⟨M, k, hk, rfl⟩ := hf
  exact ⟨M, g ≫ k, inferInstance, by simp⟩

theorem isProjOver_seq {F : Type} [Field F] {Y Y' : Scheme.{0}} (f : Y ⟶ Sp F) {B : Set Y} {s : Y' ⟶ Y}
    (h : IsSmoothBlowupSeq f B s) (hf : IsProjOver f) : IsProjOver (s ≫ f) := by
  induction h with
  | id => simpa using hf
  | @step Y₁ Y₂ s J π _ _ _ hb ih =>
    obtain ⟨X', b, hb', hproj, -⟩ := ProjBlowup.exists_blowup (s ≫ f) ih J
    obtain ⟨e, he, heb⟩ := ProjBlowup.exists_iso_of_blowup J π b hb hb'
    rw [← heb, Category.assoc]
    exact isProjOver_comp_closed e hproj

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem weak_resolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (W : Scheme.{0}) [IsIntegral W]
    (p : W ⟶ Sp F) (n : ℕ), IsProjOver p → topologicalKrullDim W = n →
    ∃ (W' : Scheme.{0}) (s : W' ⟶ W) (U : W.Opens), IsIntegral W' ∧ SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ (U : Set W).Nonempty ∧ IsIso (s ∣_ U) := by
  intro hP F _ _ W _ p n hp hdim
  obtain ⟨N, i₀, hi₀, hi₀p⟩ := hp
  obtain ⟨ℓ, hℓ, hℓs, hℓd⟩ := GlobalTheory.T.exists_linear_closedImmersion_projectiveSpace_codimTwo F N
  let i := i₀ ≫ ℓ
  let f := PSpace.str F (N + 2)
  have hif : i ≫ f = p := by simp [i, f, hℓs, hi₀p]
  have hsmf : SmoothOfRelativeDimension (N + 2) f := Adelic.smoothOfRelativeDimension_pspace F _
  have : Smooth f := by haveI := hsmf; exact SmoothOfRelativeDimension.smooth (N + 2) f
  have : IsLocallyNoetherian (PSpace F (N + 2)) := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hne, hnc⟩ := GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim i (hℓd _)
  obtain ⟨Y', s, -, -, -, hseq, -, hE, -⟩ := hP F (N + 2) _ f inferInstance hsmf
    (ProjSpace.isProjOver_pspace_str F _) i.ker hne
  rcases GlobalTheory.T.isIso_restrict_or_exists_smooth_blowup_centre_over f _ (i (genericPoint W)) s hseq with ⟨U, hU, hiso⟩ |
    ⟨Y₁, s₁, J, U, y₁, hseq₁, hsm, hJB, hU, hiso, hy₁, hs₁⟩
  · exact (hnc U hU (GlobalTheory.T.effCartier_comap_of_isIso_restrict_open s _ U hiso hE)).elim
  · obtain ⟨z, hz⟩ : ∃ z, J.subschemeι z = y₁ := by
      rw [← Set.mem_range, Scheme.IdealSheafData.range_subschemeι]; exact hy₁
    obtain ⟨W', j, hjc, hjo, hW', w', rfl⟩ := GlobalTheory.T.exists_clopen_integral_of_smooth_over_field' F J.subscheme (J.subschemeι ≫ s₁ ≫ f) hsm z
    have hg : ∀ w, (j ≫ J.subschemeι ≫ s₁) w ∈ i.ker.support := fun w =>
      hJB (Scheme.IdealSheafData.range_subschemeι J ▸ Set.mem_range_self _)
    have : IsReduced W' := inferInstance
    obtain ⟨h, hh⟩ := GlobalTheory.T.exists_lift_of_isReduced_of_mem_ker_support i (j ≫ J.subschemeι ≫ s₁) hg
    have hw' : h w' = genericPoint W := by
      apply i.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hh]
      simp [hz, hs₁]
    obtain ⟨U', hU'ne, hU'iso⟩ := GlobalTheory.T.exists_nonempty_isIso_restrict_of_generic_mem i h (j ≫ J.subschemeι) s₁ U hiso (by rw [hh]; simp)
      hU ⟨w', hw'⟩
    have hq : h ≫ p = j ≫ J.subschemeι ≫ s₁ ≫ f := by rw [← hif, reassoc_of% hh]
    have : Smooth (j ≫ J.subschemeι ≫ s₁ ≫ f) := by
      have := hsm; infer_instance
    have hpft : LocallyOfFiniteType p := by rw [← hif]; infer_instance
    have hd := GlobalTheory.T.topologicalKrullDim_eq_of_isIso_restrict' F W W' p (h ≫ p) h hpft (by rw [hq]; infer_instance) rfl U' hU'ne hU'iso
    refine ⟨W', h, U', hW', ?_, ?_, hU'ne, hU'iso⟩
    · rw [hq]; exact GlobalTheory.T.smoothOfRelativeDimension_of_integral_krullDim_eq F W' _ n inferInstance (hd.trans hdim)
    · rw [hq, ← Category.assoc]
      exact isProjOver_comp_closed _ (isProjOver_seq f hseq₁ (ProjSpace.isProjOver_pspace_str F _))

end GlobalTheory.WeakRes
