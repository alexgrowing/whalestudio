import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricHeckeSumTermAtCosetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterParahoricCosetsEqSchurCountStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

open Classical

namespace GlobalTheory.ParHeckeTarget

theorem sum_reps_datum_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, ∑ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = ∑ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s R d hR RK hRK x
  have hL : ∀ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) =
      if InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) then datum ξ x else 0 := by
    intro j hj
    have h := GlobalTheory.T.parahoric_hecke_sum_term_at_coset k A D D' ϖ hϖ ξ hξ s j (hR.1 j hj).1 (d j) (hR.1 j hj).2 x
    split_ifs with hs
    · exact h.1 hs
    · rw [h.2 hs, mul_zero]
  have hRt : ∀ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x =
      if (∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]) then datum ξ x else 0 := by
    intro g _
    simp only [liftS, intInd]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRt, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const]
  by_cases hx : InSupp x
  · rw [GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count k A D D' ϖ hϖ s R d hR RK hRK x hx]
  · have h0 : datum ξ x = 0 := by simp only [datum, dif_neg hx]
    simp [h0]

end GlobalTheory.ParHeckeTarget
