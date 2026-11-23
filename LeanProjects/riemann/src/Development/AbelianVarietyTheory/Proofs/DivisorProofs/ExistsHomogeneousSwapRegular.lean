import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularBaseRankTwoMetricFamilyStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

theorem swapReg_exists : ArCalc → ∃ G, Homog G ∧ SwapReg G := by
  intro hC
  obtain ⟨G, hG, hcore⟩ := GlobalTheory.T.regular_base_rank_two_metric_family hC
  refine ⟨G, hG, ?_⟩
  intro k _ B Y _ _ q p d hq hp hreg π w E h H hflB fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨flB⟩ := hflB
  set L5 := fam5 π w H flB fl A with hL5
  obtain ⟨Φ5, hΦ5⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 5) L5).1

  have e3 := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ hΦ5 ![0, 1, 2] (fun i => by fin_cases i <;> rfl)

  have iso : ((L5 0).tens (L5 1)).Isometric ((L5 3).tens (L5 4)) := by
    have e₁ := GlobalTheory.T.rank_two_graded_determinant_isometric k Y p _ _ (H.pull π w) fl
    have e₂ := VMetric.isometric_det_pull H π w
    have e₃ := ((GlobalTheory.T.rank_two_graded_determinant_isometric k B q E h H flB).symm.pull π w).trans (HermLB.isometric_pull_tens _ _ π w)
    exact e₁.trans (e₂.trans e₃)
  have icl : (L5 1).icls = (L5 3).icls + (L5 4).icls - (L5 0).icls := by
    have := HermLB.icls_eq_iff.2 iso
    rw [HermLB.icls_tens, HermLB.icls_tens] at this
    rw [← this]
    abel

  let T : Fin 5 → Fin 5 → ℤ := fun j => if j = 1 then ![-1, 0, 0, 1, 1] else Pi.single j 1
  have hT : ∀ j, (comb L5 (T j)).Isometric (L5 j) := by
    intro j
    by_cases hj : j = 1
    · subst hj
      refine HermLB.icls_eq_iff.1 ?_
      rw [icls_comb, icl]
      simp [T, Fin.sum_univ_five]
      abel
    · simp only [T, hj, if_false]
      exact isometric_comb_single L5 j
  have hsub := ((hC.arIso k Y p (d + 1) hp).2 (Fin 5) L5 Φ5 hΦ5).2.2 (Fin 5) L5 T hT
  have e5 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ5 hsub
  have eline : Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Φ5 (onLine d a b) := by
    rw [← map_add, e3, LinearMap.comp_apply, AlgHom.toLinearMap_apply, e5, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    change Φ5 (aeval _ (rename _ (swapSum d a b))) = _
    rw [onLine, aeval_rename]
    congr 2
    congr 1
    funext i
    fin_cases i <;> simp [T, lin, Fin.sum_univ_five, Pi.single_apply] <;> ring

  have hdim : topologicalKrullDim (closure ({π (genericPoint Y)} : Set B)) < ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (topologicalKrullDim_subspace_le B _).trans_lt ?_
    rw [hq.dim_eq]
    exact_mod_cast Nat.lt_succ_self (d + 1)
  let LB3 : Fin 3 → HermLB q := ![VMetric.grLB flB 1 H, VMetric.grLB flB 0 H, A]
  let L3 : Fin 3 → HermLB p := fun i => (LB3 i).pull π w
  obtain ⟨Φ3, hΦ3⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 3) L3).1
  have z3 : IsArFun L3 (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply]
    exact (isometric_comb_pull LB3 n π w).symm.isSelfInter hp
      (GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w hdim (comb LB3 n))
  have e3' := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ3 hΦ5 ![4, 3, 2] (fun i => by fin_cases i <;> rfl)
  have ebase : Φ5 (onBase d a b) = 0 := by
    have h0 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ3 z3
    have : onBase d a b = rename ![(4 : Fin 5), 3, 2] (swapSum d a b) := by
      rw [onBase, ← aeval_X_left_apply (rename _ _), aeval_rename]
      congr 2
      funext i
      fin_cases i <;> rfl
    rw [this, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, ← e3', h0, LinearMap.zero_apply]

  rw [eline, show onLine d a b = onBase d a b + (onLine d a b - onBase d a b) by ring, map_add, ebase, zero_add]
  exact hcore k B Y q p d hq hp hreg π w E h H flB fl hfl A Φ5 Ψ hΦ5 hΨ a b

end GlobalTheory.CovTest.SwapLine

end
