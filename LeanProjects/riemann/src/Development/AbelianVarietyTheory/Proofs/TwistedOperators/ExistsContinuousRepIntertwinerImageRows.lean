import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLeftInvariantRepConjugateTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowRepR

private theorem lamS_eq_lamAt (R : Ranks) (P : HCParam R) (i : Fin R.r) :
    Formalism.MainNotions.S.lamS R P i = ((Formalism.L2.NTheta.lamAt P i.val : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS Formalism.L2.NTheta.lamAt
  by_cases h1 : i.val < R.k - 1
  · simp [h1]
  · by_cases h2 : i.val - (R.k - 1) < R.m
    · simp [h1, h2]
    · simp [h1, h2]

private theorem gapGe_hundred_mul_r_pow_four {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hH : HostHyp D) :
    GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) := by
  intro v
  unfold Formalism.QuantumDeterminants.GapAtLeast
  intro a b hab
  rw [X.eps_eq, X.eps_eq] at hab
  rw [X.lam_eq, X.lam_eq, lamS_eq_lamAt, lamS_eq_lamAt]
  have key : ∀ i j : Fin D.R.r, i.val < j.val →
      100 * (D.R.r : ℝ) ^ 4 ≤ |((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ)| := by
    intro i j hij
    have hq := GlobalTheory.DSGapData.lamAt_gap hH (X.pl v) i.val j.val hij j.isLt
    have hr : 100 * (D.R.r : ℝ) ^ 4 ≤ ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) i.val : ℚ) : ℝ) -
        ((Formalism.L2.NTheta.lamAt (D.hc (X.pl v)) j.val : ℚ) : ℝ) := by exact_mod_cast hq
    exact hr.trans (le_abs_self _)
  have hne : (Fin.cast X.n_eq a).val ≠ (Fin.cast X.n_eq b).val := fun hv => hab (congrArg _ (Fin.ext hv))
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact key _ _ hlt
  · rw [abs_sub_comm]
    exact key _ _ hgt

theorem exists_contRep_rows : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → ∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM hH hE t c ht hconj hc Φ hΦ u
  exact GlobalTheory.ConjRowRep.exists_contRep hDS D X h R.θ _ (MP R) _ _ t c rfl hM.inf (gapGe_hundred_mul_r_pow_four X hH) hE
    ⟨ht, hconj⟩ hc Φ hΦ u

end GlobalTheory.ConjRowRepR

end
