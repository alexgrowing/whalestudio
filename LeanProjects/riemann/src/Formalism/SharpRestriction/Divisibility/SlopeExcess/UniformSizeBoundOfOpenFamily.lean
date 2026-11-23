import Mathlib
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.NormDecompositionCondOfJetConsequence
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions

theorem top2c2_wj_nonneg {D : D7} (L : SizeData₂ D) (j : ℕ) (τ : D.what₂.Tau) : 0 ≤ wj D j τ := by
  by_cases h : j - 1 < D.R.m
  · have hj1 : 1 ≤ max j 1 := le_max_right _ _
    have hj2 : max j 1 ≤ D.R.m := by omega
    have h' : max j 1 - 1 < D.R.m := by omega
    have key := S.wj_ge L τ (max j 1) hj1 hj2
    have hp := S.w''_pos L
    unfold wj at key ⊢
    rw [dif_pos h]
    rw [dif_pos h'] at key
    have hf : (⟨max j 1 - 1, h'⟩ : Fin D.R.m) = ⟨j - 1, h⟩ := Fin.ext (by show max j 1 - 1 = j - 1; omega)
    rw [hf] at key
    linarith
  · unfold wj; rw [dif_neg h]

theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h

theorem uniform_size_bound_of_open_family {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hG : DGamSize Fm)
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch) (C1 C2 C3 : ℝ)
    (hC : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      LiftErrorLocal.JetConsequence (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1 C2 C3)
    (hB : product_first_zeroth_parts.BudF Fm)
    (hSz : ∃ Cg x0 : ℝ, 0 ≤ Cg ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
      WeightDegreeSizes.TypePrimeSizeBound (Fm.D x i) (Fm.L x i) Fm.cX.err (max C3 0 + 2 * max weightDegreeConstant 0) Cg)
    (hD : ∃ Cd x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.DiscriminantOffsetBound (Fm.D x i) (Fm.L x i) Cd)
    (hI : ∃ CI x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.InertPrimeLossBound (Fm.D x i) (Fm.L x i) Fm.GK Fm.cX.err CI) :
    LocalQuadraticParts.ComplementTwoFamily Fm := by
  obtain ⟨CT, xT, hOT⟩ := J.family_levelPrime_budget Fm hT (top2c2_dlSize eps Fm) hB
  obtain ⟨CG, xG, hOG⟩ := J.family_gammaDiscriminant_budget Fm hT (top2c2_dlSize eps Fm) hG
  obtain ⟨Cg, xs, hCg, hSz⟩ := hSz
  obtain ⟨Cd, xd, hD⟩ := hD
  obtain ⟨CI, xi, hI⟩ := hI
  obtain ⟨C, x0, h⟩ := degree_weight_family_of_constant Fm XF C1 C2 C3 hC ⟨0, fun x _ i j τ => top2c2_wj_nonneg (Fm.L x i) j τ⟩
    ⟨Cg, CT, CG, Cd, CI, max (max xT xG) (max xs (max xd xi)), hCg, fun x hx i => by
      simp only [max_le_iff] at hx
      exact ⟨hSz x hx.2.1 i, hOT x hx.1.1 i, hOG x hx.1.2 i, hD x hx.2.2.1 i, hI x hx.2.2.2 i⟩⟩
  refine ⟨C, max x0 (Fm.x1 + 1), fun x hx i => h x (le_trans (le_max_left _ _) hx) ?_ i⟩
  have := le_trans (le_max_right _ _) hx
  linarith

end Formalism.MainNotions.DIV.Proofs
