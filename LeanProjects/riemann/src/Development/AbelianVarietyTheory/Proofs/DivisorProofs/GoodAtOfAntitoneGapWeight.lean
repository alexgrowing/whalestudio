import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeFinitelyGeneratedAltBis
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  refine ⟨hasGram_nrm_of_good D T j Y e o hY G', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

theorem goodAt_shiftG : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : ℤ), Even n → (∀ τ, Antitone ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ)) → (∀ τ, 1 ≤ gap ((laOf (T.Q.Dw j) a n + s • hodgeWt (T.Q.Dw j)) τ) ((T.Q.Dw j).p - 1)) → Y.GoodAt (shiftG (T.Q.Dw j) a n s) := by
  intro hP D T hT j hp hq hf hj Y e o hY a n s hn hA hg
  obtain ⟨m, rfl⟩ := hn
  have hmul : ∀ k : ℕ, Y.GoodAt (wtOf _ ((k + 1) • (laOf (T.Q.Dw j) a (m + m) + s • hodgeWt (T.Q.Dw j))) 0) := by
    intro k
    refine (GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hf hj Y e o hY _ (fun τ => ?_) (fun τ => ?_)).1
    · intro x y hxy
      simp only [Pi.smul_apply]
      exact nsmul_le_nsmul_right (hA τ hxy) _
    · have := hg τ
      simp only [Pi.smul_apply]
      unfold gap at this ⊢
      split_ifs at this ⊢ with h1
      · simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        have hk : (1 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos k
        rw [← mul_sub]
        exact this.trans (le_mul_of_one_le_left (by linarith) hk)
      · exact this
  refine goodAt_of_exZ hY ?_ ⟨hasGram_nrm_of_good D T.toCore j Y e o hY _,
    GlobalTheory.T.latW_fg_of_good hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m,
    GlobalTheory.T.weight_lattice_span_eq hP D T hT j hp hq hf hj Y e o hY _ hA hg hmul m⟩
  rw [← two_mul, GlobalTheory.CovTop.Model.exZ_shiftG]
  rfl

end GlobalTheory.CovTop.ShiftGood

end
