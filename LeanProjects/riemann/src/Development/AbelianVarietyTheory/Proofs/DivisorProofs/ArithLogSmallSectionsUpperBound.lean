import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefHermitianSmallSectionsKeyInequalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeAddMulLogSqOfLeAddMulLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsPairSumRatFnFamilyTensorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.lc_le_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (x : Fin D → X.functionField) (β : ℝ) (q : ℕ), AlgebraicIndependent ℤ x → (∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1) → (P.L.tens P.A).IsNef D → (P.L.tens P.A).IsSelfInter β → 3 ≤ q → P.lc 1 0 1 ≤ bound D q β (gdeg (P.L.tens P.A) D) := by
  intro hC hA hS k _ X _ p D hX P x β q hx hxB hNef hSI hq
  haveI := hX.charZero
  haveI hcz : CharZero X.functionField :=
    charZero_of_injective_ringHom (f := (X.germToFunctionField ⊤).hom) (X.germToFunctionField_injective ⊤)
  have hβ : 0 ≤ β := by
    obtain ⟨h, hh, rfl⟩ := hSI
    exact (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX _ hNef).2 h hh _
  have hg : 0 ≤ gdeg (P.L.tens P.A) D := GlobalTheory.T.hermLineBundleGeometricDegree_nonneg_of_semiPos k X p D hX _ hNef.semiPos
  have hq' : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hΔ : 0 < Real.log ((q:ℝ)/2) := Real.log_pos (by linarith)
  have hF : (0:ℝ) < ((D+1).factorial : ℝ) := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hFD : 0 < ((D+1).factorial : ℝ) * Real.log ((q:ℝ)/2) := mul_pos hF hΔ
  set g := gdeg (P.L.tens P.A) D with hgdef
  set Δ := Real.log ((q:ℝ)/2) with hΔdef
  set α := (β + (D + 1) * (Δ + D * Real.log 2 / 2) * g) / ((D + 1).factorial * Δ) with hαdef
  set β' := (D + 1) * g / (2 * ((D + 1).factorial * Δ)) with hβ'def
  have hα : 0 ≤ α := div_nonneg (by positivity) hFD.le
  have hβ' : 0 ≤ β' := div_nonneg (by positivity) (by positivity)
  have hT : 0 ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) :=
    add_nonneg hα (mul_nonneg hβ' (Real.log_nonneg (by nlinarith)))
  have hexp : ∀ m : ℕ, (2 / q : ℝ) ^ m = Real.exp (-(m * Δ)) := by
    intro m
    have e1 : (2 / q : ℝ) = Real.exp (-Δ) := by
      rw [Real.exp_neg, hΔdef, Real.exp_log (by positivity), inv_div]
    rw [e1, ← Real.exp_nat_mul]
    congr 1
    ring
  have key : ∀ (r : ℕ) (e : Fin r → X.functionField) (n : Fin r → ℕ), LinearIndependent ℤ e →
      (∀ j, e j ∈ P.Bl 1 0 ((2 / q : ℝ) ^ n j)) →
      ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log ((α + 2 * β' + 1) ^ 2) := by
    intro r e n he hB
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simpa using hT
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    have hsmall : SmallFam (P.L.tens P.A) (boxFam e x) (fun c => n c.1 * Δ) := by
      apply GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor k X p P
      rintro ⟨j, S⟩
      have h1 := hB j
      have h2 := hxB S
      obtain ⟨hm, hnu⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P 1 0 0 1 _ _ h1.1 h2.1
      have e10 : ((1:ℤ) + 0) = 1 := by norm_num
      have e01 : ((0:ℤ) + 1) = 1 := by norm_num
      rw [e10, e01] at hm hnu
      refine ⟨hm, fun σ y => ?_⟩
      show P.nu 1 1 σ y (e j * ∏ i ∈ S, x i) ≤ _
      rw [hnu, ← hexp]
      have h0 : 0 ≤ P.nu 1 0 σ y (e j) := by unfold Pair.nu; positivity
      exact (mul_le_of_le_one_right h0 (h2.2 σ y)).trans (h1.2 σ y)
    have hcore := GlobalTheory.T.nef_hermitian_small_sections_key_inequality hC hA hS k X p D hX _ β hNef hSI x Δ hx hΔ (Fin r) e n he hsmall
    rw [Fintype.card_fin] at hcore
    have hrs : (r:ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      have : r ≤ ∑ j : Fin r, (n j + 1) := by
        calc r = ∑ _j : Fin r, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun j _ => by omega)
      exact_mod_cast this
    have hs : ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ α + β' * Real.log r := by
      have e2 : α + β' * Real.log r =
          (β + ((D:ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log r / 2) * g) / ((D + 1).factorial * Δ) := by
        rw [hαdef, hβ'def]
        field_simp
        ring
      rw [e2, le_div_iff₀ hFD]
      linarith
    exact GlobalTheory.le_add_mul_log_sq_of_le_add_mul_log α β' r _ hα hβ' (by exact_mod_cast hr) hrs hs
  have hfin := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P 1 0 1
  exact GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound X.functionField (P.H 1 0) (P.Bl 1 0) (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0) hfin q _ hq hT key
