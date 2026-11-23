import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → P.L.SemiPos D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hamp hsp J _ e x he hx hbox
  have hxb := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  have hmono := (GlobalTheory.VolBr.isBallFam_mono_neg_add _ _ _ (GlobalTheory.VolBr.Pair.isBallFam k X p P 1 0)).1
  have hb : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ P.Bl 1 0 (Real.exp u) := fun c =>
    GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P 1 0 _ (hbox c)
  choose u hu0 hu using hb
  have hall : ∀ c, boxFam e x c ∈ P.Bl 1 0 (Real.exp (∑ c, u c)) := fun c =>
    hmono _ _ (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c))) (hu c)
  apply GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX P 1 0 P.L (GlobalTheory.VolBr.Pair.rep_base k X p P).1 hamp hsp
    (Fintype.card J) (∑ c, u c)
  intro m hm
  rcases isEmpty_or_nonempty J with hJ | ⟨⟨j⟩⟩
  · have h0 : Fintype.card J = 0 := Fintype.card_eq_zero
    haveI : IsEmpty (Fin (Fintype.card J * m ^ D)) := by rw [h0, zero_mul]; exact Fin.isEmpty'
    exact ⟨isEmptyElim, linearIndependent_empty_type, isEmptyElim⟩
  · haveI : CharZero X.functionField := charZero_of_inj_zero fun n hn => by
      have h := he.smul_left_injective j (a₁ := (n : ℤ)) (a₂ := 0) (by simp [hn])
      exact_mod_cast h
    obtain ⟨v, hv, hvs⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x hxb J e he m hm
    refine ⟨v, hv, fun s => ?_⟩
    obtain ⟨w, n, hn, hvs'⟩ := hvs s
    rw [hvs']
    have h := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p P D J e x 1 0 (Real.exp (∑ c, u c)) (Real.exp_pos _).le hall m w n hn
    rw [← Real.exp_nat_mul, mul_comm (m : ℝ)] at h
    exact h
