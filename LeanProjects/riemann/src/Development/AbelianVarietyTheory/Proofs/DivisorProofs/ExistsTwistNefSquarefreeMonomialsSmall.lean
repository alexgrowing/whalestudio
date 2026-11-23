import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermPairSectionsChangeOfIsometricCombinatiStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef.BoxTwist

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_shift_tens (N M : HermLB p) (u : ℝ) :
    ((N.tens M).shift (fun _ => u) fun _ => rfl).Isometric (N.tens (M.shift (fun _ => u) fun _ => rfl)) :=
  HermLB.isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => (add_assoc _ _ _).symm

variable [IsIntegral X]

theorem isRatSec_const_mul {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (g : X.functionFieldˣ) :
    IsRatSec B fun i => g * r i := fun a b h => by
  beta_reduce
  rw [Units.val_mul, Units.val_mul, hr a b h]
  ring

theorem exists_pair_small (Q : Pair p) (W : HermLB p) (g : X.functionField) (hg : g ≠ 0) (u : ℝ) :
    ∃ P : Pair p, P.L = W ∧ P.A = Q.A.shift (fun _ => u) (fun _ => rfl) ∧
      ∀ f, g * f ∈ Q.Bl 0 1 (Real.exp u) → f ∈ P.Bl 0 1 1 := by
  obtain ⟨r, hr⟩ := exists_isRatSec W.isLB
  let P : Pair p := ⟨W, Q.A.shift (fun _ => u) (fun _ => rfl), r, fun j => Units.mk0 g hg * Q.r' j, hr,
    isRatSec_const_mul Q.hr' _⟩
  have e (f i i' j) : P.loc 0 1 f i j = Q.loc 0 1 (g * f) i' j := by
    simp only [Pair.loc, P, zpow_zero, zpow_one, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨P, rfl, rfl, fun f hf => ⟨fun x i j _ hj => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨i', hi'⟩ := exists_chart Q.L.isLB x
    rw [e f i i' j]
    exact hf.1 x i' j hi' hj
  · have h := hf.2 σ y
    have e' : P.nu 0 1 σ y f = Q.nu 0 1 σ y (g * f) * Real.exp (-u) := by
      rw [Pair.nu, Pair.nu, e f _ (pick (Q.L.φ σ).isLB y), mul_assoc, ← Real.exp_add]
      congr 2
      have : (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y = (Q.A.φ σ).φ (pick (Q.A.φ σ).isLB y) y + 2 * u := rfl
      rw [this]
      push_cast
      ring
    rw [e']
    calc _ ≤ Real.exp u * Real.exp (-u) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem exists_twist : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  intro hC k _ X _ p D hX N x
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair N A
  obtain ⟨c, g, -, hg, -, hgf⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P hA (-1) (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  choose v hv0 hv using fun S => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX P (-1) c _ (hgf S)
  let u : ℝ := ∑ S, v S
  have hu : 0 ≤ u := Finset.sum_nonneg fun S _ => hv0 S
  have hvu (S) : v S ≤ u := Finset.single_le_sum (fun S _ => hv0 S) (Finset.mem_univ S)
  let M : HermLB p := P.L.dual.tens (P.A.pow c)
  obtain ⟨h₁, h₂, -⟩ := Pair.rep_base k X p P
  have hM : P.Rep (-1) c M := by
    simpa using Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_dual k X p P _ _ _ h₁) (Pair.rep_pow k X p P _ _ _ c h₂)
  obtain ⟨Q, -, hQ, hB⟩ := GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations k X p P _ _ _ _ M M hM hM
  have hi : (P.A.pow c).Isometric (P.L.tens M) :=
    HermLB.icls_eq_iff.1 (by simp only [M, HermLB.icls_tens, HermLB.icls_dual]; abel)
  have hn : (P.L.tens M).IsNef D :=
    (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ hi).2.1 (GlobalTheory.NefPow.isNef_pow hC k X p D hX _ c hAn)
  refine ⟨M.shift (fun _ => u) fun _ => rfl, (GlobalTheory.T.hermitianLineBundle_positivity_preserved_isometric hC k X p D hX _ _ (isometric_shift_tens _ _ u)).2.1
    (GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX _ u hu hn), fun W => ?_⟩
  obtain ⟨R, hR, hR', h⟩ := exists_pair_small Q W g hg u
  refine ⟨R, hR, by rw [hR', hQ], fun S => h _ ?_⟩
  rw [hB]
  simp only [zero_mul, one_mul, zero_add]
  exact ⟨(hv S).1, fun σ y => ((hv S).2 σ y).trans (Real.exp_le_exp.2 (hvu S))⟩

end GlobalTheory.HSNef.BoxTwist
