import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomPairsSmallReferenceTupleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop GlobalTheory.NormSum Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.ArchGrid

theorem level_pos {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) : 0 < Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | h
  · have h1 := P.idx_le
    rw [zero_pow (by positivity)] at h1
    exact absurd (Nat.le_zero.1 h1) P.idx_ne
  · exact h

theorem arch_grid : GlobalTheory.SqTop.GBig fun {D} _ _ {sc} G μ₀ C _ b => ∀ (zA zA' : Fin D.R.m × Fin D.R.m → D.what₂.LL), (∃ δ t0 : ℂ, ∀ ij : Fin D.R.m × Fin D.R.m, ∃ P P' : Pair D ⊤ δ t0 (levQ G.pl), IsBottom G μ₀ ij.1 ij.2 (SqNum.condE G.pl) P P' ∧ D.what₂.embLL (zA ij) = (P.norm : ℂ) ∧ D.what₂.embLL (zA' ij) = (P'.norm : ℂ)) → ArchimedeanHeightBound zA zA' (C * D.R.f * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ) * (Real.log b + Real.log ((maxWt D sc.cGap : ℝ) * (2 * (bigN D : ℝ)))) + C * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D sc.cGap : ℝ))) + C * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl)) := by
  obtain ⟨C0, -, hA⟩ := GlobalTheory.ArchFree.st.archSt
  refine ⟨0, fun ε CF _ => ⟨C0, 0, fun C hC D large₂ _ _ hR T Lc μ₀ hμ G => ?_⟩⟩
  rintro zA zA' ⟨δ, t0, h⟩
  choose P P' hB hz hz' using h
  haveI := D.tcLL
  obtain ⟨-, -, hf4, hm44, -, -, -, -, -, hrd1, hrd2, -⟩ := hR.size
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  have hB1 : (1 : ℝ) ≤ (maxWt D 1 : ℝ) := by exact_mod_cast le_max_left _ _
  have hrd : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
  have hdl : |TaylorLogMetric.logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
    rw [hlb]
    have e : TaylorLogMetric.logDerivativeAtOne D = large₂.logDerivativeAtOne := by rw [large₂.logDerivative_at_one_eq]; rfl
    rw [e]; exact hR.dlog
  intro ij
  have hQ : 0 < levQ G.pl := level_pos (P ij)
  have key := hA D ⊤ δ t0 (levQ G.pl) (P ij).crv (P ij).pt0 hQ D.what₂.LL D.what₂.embLL (Fin D.R.m × Fin D.R.m) (bigN D)
    (maxWt D 1 : ℝ) (Real.log large₂.sc.b) P P' zA zA' hN hB1 (by rw [hlb]; exact hL1) hrd hdl
    (fun k => GlobalTheory.T.squareBottomPairs_small_reference_tuple hμ G δ t0 _ (P k) (P' k) k.1 k.2 _ (hB k)) (fun k => ⟨hz k, hz' k⟩) ij
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf4
    exact_mod_cast this
  have hN' : (1 : ℝ) ≤ (bigN D : ℝ) := by exact_mod_cast hN
  have hX : 0 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) := by
    have h1 : 0 ≤ Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ))) := Real.log_nonneg (by nlinarith)
    have h2 : 0 ≤ Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ)) := by
      apply Real.log_nonneg
      have : 1 ≤ (D.R.f : ℝ) * (2 * (bigN D : ℝ)) := by nlinarith
      nlinarith
    have h3 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
    have hl : 0 ≤ Real.log large₂.sc.b := by rw [hlb]; linarith
    positivity
  have hle : ∀ c : ℝ, c * (D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      c * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      c * (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ) = c * ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ) *
      (Real.log large₂.sc.b + Real.log ((maxWt D 1 : ℝ) * (2 * (bigN D : ℝ)))) +
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + Real.log ((D.R.f : ℝ) * (2 * (bigN D : ℝ)) * (maxWt D 1 : ℝ))) +
      (bigN D : ℝ) ^ 2 * Real.log (levQ G.pl : ℝ)) := fun c => by ring
  have hmono := mul_le_mul_of_nonneg_right hC hX
  show _ ∧ _
  constructor
  · refine le_trans key.1 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm
  · refine le_trans key.2 (le_of_eq_of_le ?_ (le_of_le_of_eq hmono ?_))
    · exact (hle C0).symm ▸ rfl
    · exact (hle C).symm

end GlobalTheory.ArchGrid
