import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepGood

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fixedOK_of_rows (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ what₂) : FixedOK D F0 Λ := by
  obtain ⟨hE, hz, hrr, -⟩ := hR
  obtain ⟨-, ⟨hlat, hunim, -, -⟩, hx⟩ := hrr.1 Λ hΛ
  refine ⟨hlat, hunim, hE, ?_, (D.cOf u)⁻¹, inv_ne_zero (D.cOf_ne u), ?_⟩
  · unfold XLam at hx
    intro a
    have hmem : F0.e a ∈ XS D F0 := by
      unfold XS
      clear hrr hz hunim hlat hΛ what₂ hE hx
      apply Submodule.subset_span
      refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
      unfold ddS
      have hne : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
        Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
      have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
        have := a.isLt
        omega
      rw [hk, zpow_neg, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ hne))]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hx] at hmem
    exact hmem.1
  · rw [hz]
    rfl

theorem orbitReps_of (hN : UnipotentIntegralIsGroup) (hRk : RankG) (hG : GoodEZ) (h1 : Stage1) (h2 : Stage2) (hK : FinK) :
    OrbitReps := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hF := fixedOK_of_rows D u F0 what₂ hR hΛ
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F1, hF1⟩ := hne
    have hGZ : GZ (Tn u) (Tn u') Z ≠ 0 := by
      have h := hF1.1.2.2
      rw [gz_eq, hF1.2.2.2.2] at h
      exact h
    obtain ⟨R, hRm⟩ := hRk D (Tn u) (Tn u') Z hGZ
    obtain ⟨Wf, hWf, hW⟩ := h1 D (Tn u') F0 Λ hF Z R hRm
    obtain ⟨Af, hAf, hAx⟩ := h2 D (Tn u') F0 Λ hF Z R hRm Wf hWf
    refine ⟨{x | Good D (Tn u') F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af},
      hK D (Tn u') F0 Λ hF Z R hRm Wf Af hWf hAf, fun F' hF' => ?_⟩
    have g0 := hG D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n1, hn1, hw1⟩ := hW _ g0
    have g1 := good_move D (Tn u') F0 Λ Z g0 hn1
    obtain ⟨n2, hn2, hw2, ha2⟩ := hAx _ g1 hw1
    have g2 := good_move D (Tn u') F0 Λ Z g1 hn2
    refine ⟨n1.trans n2, (hN D F0 Λ).2.2 n1 hn1 n2 hn2, ?_⟩
    have hact : act D (n1.trans n2) (F'.fl.e, F'.fl.z) = act D n2 (act D n1 (F'.fl.e, F'.fl.z)) := rfl
    show act D (n1.trans n2) (F'.fl.e, F'.fl.z) ∈ _
    rw [hact]
    exact ⟨g2, hw2 ▸ hw1, ha2⟩
  · refine ⟨∅, Set.finite_empty, fun F' hF' => absurd ⟨F', hF'⟩ hne⟩

end PI.UnitaryGroupMassFormula.CntFormula
