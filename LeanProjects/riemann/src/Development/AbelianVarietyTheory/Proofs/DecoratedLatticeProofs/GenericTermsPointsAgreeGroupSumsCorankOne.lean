import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
