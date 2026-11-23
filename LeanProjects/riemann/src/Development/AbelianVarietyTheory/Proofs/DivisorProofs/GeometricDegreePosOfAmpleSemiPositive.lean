import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulCardLeDegreeAmpleSemiPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_pair_mem_H_of_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {a b : ℤ} {M : HermLB p} (h : P.Rep a b M) : ∃ Q : Pair p, Q.L = M ∧ ∀ f ∈ P.H a b, f ∈ Q.H 1 0 := by
  obtain ⟨ρ, hρ, hu, -⟩ := h
  refine ⟨⟨M, P.A, ρ, P.r', hρ, P.hr'⟩, rfl, fun f hf x c j hc hj => ?_⟩
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  have h1 := (hu x c i j hc hi hj).regAt.mul (hf x i j hi hj)
  have hi0 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (P.r i).ne_zero
  have hj0 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (P.r' j).ne_zero
  convert h1 using 1
  simp only [Pair.loc, zpow_one, zpow_zero]
  field_simp

theorem gdeg_pos_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, IsAmpleLB L.B → L.SemiPos D → 0 < gdeg L D := by
  intro hA hS k _ X _ p D hX L hL hs
  obtain ⟨P, rfl, hPA⟩ := exists_pair L L
  obtain ⟨x, hx⟩ := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).1
  obtain ⟨c, g, hc, hg, -, hm⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P (hPA ▸ hL) 0 (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  have hr := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
  rw [mul_zero, mul_one, hPA] at hr
  obtain ⟨Q, hQ, hH⟩ := exists_pair_mem_H_of_rep P hr
  have hQa : IsAmpleLB Q.L.B := by
    rw [hQ]
    exact (isAmpleLB_pow_iff hL.isLB hc).2 hL
  have hQs : Q.L.SemiPos D := by rw [hQ]; exact hs.pow c
  haveI : CharZero X.functionField :=
    have := hX.charZero
    ((fnOf (X := X) ⊤ trivial).charZero_iff (fnOf_injective _ _)).1 this
  have hli : LinearIndependent ℤ (fun _ : Unit => g) := linearIndependent_unique_iff.2 hg
  have h := GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive hA hS k X p D hX Q hQa hQs Unit (fun _ => g) x hli hx.1 fun c' => hH _ (hm c'.2)
  rw [hQ, GlobalTheory.T.hermLineBundleGeometricDegree_pow hA k X p D hX] at h
  have h0 : (0 : ℝ) < (c : ℝ) ^ D := by positivity
  have h1 : (0 : ℝ) < (D.factorial : ℝ) * Fintype.card Unit := by
    simp [Nat.factorial_pos]
  exact (mul_pos_iff_of_pos_left h0).1 (h1.trans_le h)

end GlobalTheory.HSNef
