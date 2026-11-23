import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.TransposeEqOfPosSemidef
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace CuspCovolume

theorem periodGram_castAdd {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : Fin g) :
    periodGram τ (Fin.castAdd g k) (Fin.castAdd g k) = (τ.map Complex.im)⁻¹ k k := by
  simp only [periodGram, of_apply, periodBasis, Fin.append_left]
  rw [show hermPair (τ.map Complex.im)⁻¹ (Pi.single k 1) (Pi.single k 1) =
      hermValue (τ.map Complex.im)⁻¹ (Pi.single k 1) from rfl, MCSchur.hermValue_eq_qf]
  have h1 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).re) = Pi.single k (1 : ℝ) := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  have h2 : (fun j => ((Pi.single k (1 : ℂ) : Fin g → ℂ) j).im) = 0 := by
    ext j
    by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [h1, h2]
  simp [MCSchur.qf, mulVec_single]

theorem inv_diag_le_of_ge {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) {c : ℝ}
    (hc : 0 < c) (h : ∀ x : Fin g → ℝ, c * ∑ k, x k ^ 2 ≤ MCSchur.qf Y x) (k : Fin g) :
    Y⁻¹ k k ≤ 1 / c := by
  refine MCCusp.inv_diag_le hY k hc fun x => ?_
  have hs : x k ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg (x j)) (Finset.mem_univ k)
  have := h x
  nlinarith

end CuspCovolume

theorem CuspCovolume.proof (hImPos : ChartPeriodImPos.Statement)
    (hPG : PeriodGramPosDef.Statement) (hCB : CuspCoordinateBound.Statement)
    (hPB : PivotBounds.Statement) (hGP : GramPivotProduct.Statement)
    (hPP : PivotProductBound.Statement) (hLC : PeriodLatticeCovolume.Statement)
    (hLead : LeadingCovolume.Statement) : CuspCovolume.Statement := by
  intro D T
  obtain ⟨ε, hε, hεb⟩ := hCB D T
  set κ : ℝ := min 1 ε ^ (D.g + D.g) * (max 1 (1 / D.c))⁻¹ ^ T.r with hκ
  have hκpos : 0 < κ := by
    have h1 : 0 < min 1 ε := lt_min one_pos hε
    have h2 : 0 < max 1 (1 / D.c) := lt_max_of_lt_left one_pos
    positivity
  refine ⟨Real.sqrt κ, Real.sqrt_pos.mpr hκpos, ?_⟩
  intro p hpK hpU ℓ hℓ k v hv hind
  set τ := D.period p.1 ℓ with hτ
  obtain ⟨hYpos, hYc⟩ := hImPos D p.1 hpU ℓ hℓ
  have hS : (periodGram τ).PosDef := (hPG D.g τ hYpos).1
  obtain ⟨N, -, hN, hcov⟩ := hLC D.g τ k v hv hind
  obtain ⟨P, hPd, hPdet⟩ := hGP (D.g + D.g) (periodGram τ) hS k N hN
  have hlow : ∀ i, i < T.r → pivot (periodGram τ) i ≤ 1 / D.c := by
    intro i hi
    have hig : i < D.g := lt_of_lt_of_le hi T.r_le
    have hb := (hPB (D.g + D.g) (periodGram τ) hS (Fin.castAdd D.g ⟨i, hig⟩)).1
    simp only [Fin.val_castAdd] at hb
    rw [CuspCovolume.periodGram_castAdd] at hb
    exact hb.trans (CuspCovolume.inv_diag_le_of_ge hYpos D.c_pos hYc _)
  have hhigh : ∀ i, T.r ≤ i → i < D.g + D.g → ε ≤ pivot (periodGram τ) i := by
    intro i hri hid
    exact (hPB (D.g + D.g) (periodGram τ) hS ⟨i, hid⟩).2 ε hε fun y =>
      hεb p hpK hpU ℓ hℓ y ⟨i, hid⟩ hri
  have hprod := hPP (D.g + D.g) T.r (periodGram τ) hS (T.r_le.trans (Nat.le_add_right _ _))
    (1 / D.c) ε hε hlow hhigh P hPd
  rw [hcov, hLead D.g τ T.r T.r_le, ← Real.sqrt_mul hκpos.le]
  exact Real.sqrt_le_sqrt (hprod.trans hPdet)

end

end GroundTheory.Heights₂.Heights
