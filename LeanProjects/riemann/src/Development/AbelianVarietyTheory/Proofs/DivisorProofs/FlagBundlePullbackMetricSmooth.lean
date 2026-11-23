import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoEmbeddingsOfTranscendental
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionFormExists
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

theorem arFun_sumLine_base_eq_zero : ArCalc → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf), Nonempty (Vert.Flag E 2) →
    ∀ (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ),
      IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ →
      IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ →
      ∀ P : MvPolynomial (Fin 2) ℝ, P.IsHomogeneous (d + 2) →
        Φ (aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ) P) = 0 := by
  intro hC k _ B Y _ _ q p d hq hp _ π w E h H _ fl _ A Φ _ hΦ _ P _
  let L4 : Fin 4 → HermLB p :=
    ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w, (VMetric.det H).pull π w]
  obtain ⟨Φ4, hΦ4⟩ := ((hC.arExists k Y p (d + 1) hp).2 (Fin 4) L4).1
  have e3 := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp hΦ hΦ4 ![0, 1, 2] (fun i => by fin_cases i <;> rfl)

  have iso : ((L4 0).tens (L4 1)).Isometric (L4 3) :=
    (GlobalTheory.VMetric.isometric_grLB_tens_grLB_det k Y p _ _ (H.pull π w) fl).trans (VMetric.isometric_det_pull H π w)
  have icl : (L4 3).icls = (L4 0).icls + (L4 1).icls := by
    have := HermLB.icls_eq_iff.2 iso
    rw [HermLB.icls_tens] at this
    exact this.symm
  let T : Fin 4 → Fin 4 → ℤ := fun j => if j = 3 then ![1, 1, 0, 0] else Pi.single j 1
  have hT : ∀ j, (comb L4 (T j)).Isometric (L4 j) := by
    intro j
    by_cases hj : j = 3
    · subst hj
      refine HermLB.icls_eq_iff.1 ?_
      rw [icls_comb, icl]
      simp [T, Fin.sum_univ_four]
    · simp only [T, hj, if_false]
      exact isometric_comb_single L4 j
  have hsub := ((hC.arIso k Y p (d + 1) hp).2 (Fin 4) L4 Φ4 hΦ4).2.2 (Fin 4) L4 T hT
  have e4 := GlobalTheory.ArInt.Model.isArFun_unique hp hΦ4 hsub

  have hdim : topologicalKrullDim (closure ({π (genericPoint Y)} : Set B)) < ((d + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (topologicalKrullDim_subspace_le B _).trans_lt ?_
    rw [hq.dim_eq]
    exact_mod_cast Nat.lt_succ_self (d + 1)
  let StrictHenselianAcyclic : Fin 2 → HermLB q := ![VMetric.det H, A]
  let L2 : Fin 2 → HermLB p := fun i => (StrictHenselianAcyclic i).pull π w
  have z2 : IsArFun L2 (d + 1) 0 := by
    refine ⟨fun n => ?_, fun _ _ _ _ => rfl⟩
    rw [LinearMap.zero_apply]
    exact (isometric_comb_pull StrictHenselianAcyclic n π w).symm.isSelfInter hp
      (GlobalTheory.ProjDrop.isSelfInter_zero_of_dim_lt hC k B Y q p d (d + 1) hq hp π w hdim (comb StrictHenselianAcyclic n))
  have e2 := GlobalTheory.VertForm.FormEx.arFun_eq_rename hC hp z2 hΦ4 ![3, 2] (fun i => by fin_cases i <;> rfl)

  have hbase : Φ4 (aeval (![X 3, X 2] : Fin 2 → MvPolynomial (Fin 4) ℝ) P) = 0 := by
    have : aeval (![X 3, X 2] : Fin 2 → MvPolynomial (Fin 4) ℝ) P = rename ![(3 : Fin 4), 2] P := by
      rw [← aeval_X_left_apply (rename _ P), aeval_rename]
      congr 2
      funext i
      fin_cases i <;> rfl
    rw [this, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, ← e2, LinearMap.zero_apply]
  rw [e3, LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← hbase]
  conv_rhs => rw [e4]
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  congr 1
  change ((rename ![(0 : Fin 4), 1, 2]).comp (aeval (![X 0 + X 1, X 2] : Fin 2 → MvPolynomial (Fin 3) ℝ))) P =
    ((aeval fun j => lin fun i => ((T j i : ℤ) : ℝ)).comp (aeval (![X 3, X 2] : Fin 2 → MvPolynomial (Fin 4) ℝ))) P
  congr 1
  ext i
  fin_cases i <;> simp [T, lin, Fin.sum_univ_four, Pi.single_apply]

end GlobalTheory.CovTest.SwapLine

end
