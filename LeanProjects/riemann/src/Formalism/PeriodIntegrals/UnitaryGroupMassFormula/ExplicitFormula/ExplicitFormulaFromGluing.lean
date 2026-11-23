import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

noncomputable section

namespace PI.EF

open Complex

theorem fractionFieldToGenericStalk_algebraMap_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = psiRaw χ u - del1 χ * u := by
  unfold psi0 psiRaw del1
  split_ifs <;> simp

theorem first_character_sum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by
  unfold S1
  exact finsum_nonneg (fun ρ => finsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem explicitFormula_of_perron_shift (κ : ℝ) (h1 : ∃ C, 0 < C ∧ PerronL C)
    (h2 : ∃ C, 0 < C ∧ ShiftBound κ C) (h3 : GoodHeightExists κ)
    (h4 : ∃ C, 0 < C ∧ TruncChange C) (h5 : ZerosFinite) : PI.ExplicitFormula := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C4, hC4, H4⟩ := h4
  refine ⟨C1 + C2 + C4, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  refine ⟨h5 N χ hχ T, ?_⟩
  obtain ⟨T', hT1, hT2, hg⟩ := h3 N χ hχ T hT
  have e1 := H1 N χ u T T' hT hTu hT1 hT2
  have e2 := H2 N χ hχ u T T' hT hTu hT1 hT2 hg
  have e4 := H4 N χ hχ u T T' hT hTu hT1 hT2
  have hS : 0 ≤ S1 χ := first_character_sum_nonneg χ
  have key : psi0 χ u + zsum χ T u = (psiRaw χ u - vertInt χ u T') +
      (vertInt χ u T' - del1 χ * u + zsum χ T' u) - (zsum χ T' u - zsum χ T u) := by
    rw [fractionFieldToGenericStalk_algebraMap_eq]; ring
  show ‖psi0 χ u + zsum χ T u‖ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ)
  rw [key]
  calc ‖(psiRaw χ u - vertInt χ u T') + (vertInt χ u T' - del1 χ * u + zsum χ T' u) -
        (zsum χ T' u - zsum χ T u)‖
      ≤ ‖psiRaw χ u - vertInt χ u T'‖ + ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ +
        ‖zsum χ T' u - zsum χ T u‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C1 * Err N u T + C2 * (Err N u T + S1 χ) + C4 * Err N u T := by gcongr
    _ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hC1.le hS, mul_nonneg hC4.le hS]

def GluePerronTrunc : Prop :=
  PerronKernel → (∃ C, 0 < C ∧ PerronSumBound C) → ∃ C, 0 < C ∧ PerronTrunc C

def GluePerronL : Prop := (∃ C, 0 < C ∧ PerronTrunc C) → ∃ C, 0 < C ∧ PerronL C

def GlueRectResidue : Prop := RectCauchy → RectResidue

def GlueGoodHeight : Prop := PI.ZerosWindow → ∃ κ, 0 < κ ∧ GoodHeightExists κ

def GlueTruncChange : Prop := PI.ZerosWindow → ∃ C, 0 < C ∧ TruncChange C

def GlueZerosFinite : Prop := PI.ZerosWindow → ZerosFinite

def GlueLocalLemma : Prop :=
  LocalAbstract → (∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C) → ZeroLocus → PI.ZerosWindow →
    ∃ C, 0 < C ∧ LocalLemma C

def GlueHoriz : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ZeroLocus → ∀ κ, 0 < κ → ∃ C, 0 < C ∧ LogDerivHoriz κ C

def GlueLeft : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ZeroLocus → ∃ C, 0 < C ∧ LogDerivLeft C

def GlueRegAtZero : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ∃ C, 0 < C ∧ RegAtZero C

def GlueContour : Prop := RectResidue → ZeroLocus → ZerosFinite → ContourIdentity

def GlueSides : Prop :=
  ∀ κ, 0 < κ → (∃ C, 0 < C ∧ LogDerivHoriz κ C) → (∃ C, 0 < C ∧ LogDerivLeft C) →
    ∃ C, 0 < C ∧ SidesBound κ C

def GlueShift : Prop :=
  ∀ κ, 0 < κ → RegularPart → ContourIdentity → (∃ C, 0 < C ∧ SidesBound κ C) →
    (∃ C, 0 < C ∧ RegAtZero C) → ∃ C, 0 < C ∧ ShiftBound κ C

theorem explicitFormula_of_leaves

    (hK : PerronKernel) (hPS : ∃ C, 0 < C ∧ PerronSumBound C) (hRC : RectCauchy)
    (hZL : ZeroLocus) (hRP : RegularPart) (hZW : PI.ZerosWindow) (hLA : LocalAbstract)
    (hG : ∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C)

    (g1 : GluePerronTrunc) (g2 : GluePerronL) (g3 : GlueRectResidue) (g4 : GlueGoodHeight)
    (g5 : GlueTruncChange) (g6 : GlueZerosFinite) (g7 : GlueLocalLemma) (g8 : GlueHoriz)
    (g9 : GlueLeft) (g10 : GlueRegAtZero) (g11 : GlueContour) (g12 : GlueSides) (g13 : GlueShift) :
    PI.ExplicitFormula := by
  obtain ⟨κ, hκ, hGood⟩ := g4 hZW
  have hLL := g7 hLA hG hZL hZW
  have hZF := g6 hZW
  exact explicitFormula_of_perron_shift κ (g2 (g1 hK hPS))
    (g13 κ hκ hRP (g11 (g3 hRC) hZL hZF) (g12 κ hκ (g8 hZW hLL hZL κ hκ) (g9 hZW hLL hZL)) (g10 hZW hLL))
    hGood (g5 hZW) hZF

end PI.EF
