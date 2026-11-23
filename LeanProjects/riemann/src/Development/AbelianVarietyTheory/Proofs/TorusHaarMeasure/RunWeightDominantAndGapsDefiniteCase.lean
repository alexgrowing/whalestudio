import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RunWeightDom

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.RunWeightDomDef

open GlobalTheory.RunWeightDom in

theorem run_weight_dom_definite : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → j = D.R.m → 8 ≤ D.R.r → ∀ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).p0 = 0 ∧ IsStrictDom ((T.U j T.σ₀).X k) (laR T j wL k) ∧ ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (a b : Fin D.R.r), (b : ℕ) = a + 1 → (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ b + 2 * (laR T j wL k τ a - laR T j wL k τ b) ≤ (laR T j wF k - kapW ((T.U j T.σ₀).X k) - WeightFamilies.dimY D j • laR T j wL k) τ a := by
  intro D T h j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hjm _ k
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : (D.R.sigW j).2 = 0 := by show D.R.m - j = 0; omega
  have hpq : (D.R.sigW j).1 + 0 = D.R.r := by
    show D.R.k + j - 1 + 0 = D.R.k + D.R.m - 1; omega
  have hz : ((T.U j T.σ₀).X k).p0 = 0 := hp0.trans hq
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    rw [hn] at bP
    exact row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
      (Int.natCast_nonneg _) _ (fun _ => 2 * (Tn : ℤ)) _ (fun _ => ((WeightFamilies.dimY D j : ℤ) + 2) * (2 * (Tn : ℤ)))
      (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hz, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)])
      (fun a => by rw [hla, hz, if_pos (Nat.zero_le _), if_pos (Nat.zero_le _)])
      bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      (fun i hi => absurd hi (by omega)) (fun i hi => absurd hi (by omega)) (by omega) (by simp)
  refine ⟨hz, fun τ => ?_, fun τ a b hab => ?_⟩
  · obtain ⟨-, k2, -, -, -⟩ := key τ
    exact ⟨fun a b _ hb => absurd hb (by omega), fun a b _ hab => k2 a b (Nat.zero_le _) hab,
      fun a b ha _ => absurd ha (by omega)⟩
  · obtain ⟨-, -, k3, -, -⟩ := key τ
    simp only [Pi.sub_apply, nsmul_eq_mul, ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW]
    exact k3 a b hab (by omega)

end GlobalTheory.RunWeightDomDef
