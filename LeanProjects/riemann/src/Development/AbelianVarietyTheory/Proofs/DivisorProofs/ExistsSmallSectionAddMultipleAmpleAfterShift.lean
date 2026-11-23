import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftSecondBundleNormPairNormBallGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionsMulMemNormMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.TwistSmall

theorem mem_regular_sections_second_bundle_indep_first {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (P : Pair p) (L' : HermLB p) (r : L'.B.ι → X.functionFieldˣ) (hr : IsRatSec L'.B r)
    {s : X.functionField} (hs : s ∈ P.H 0 1) :
    s ∈ (⟨L', P.A, r, P.r', hr, P.hr'⟩ : Pair p).H 0 1 := by
  intro x i j _ hj
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i', hi'⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  simpa [Pair.loc] using hs x i' j hi' hj

theorem le_dual_pow_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (N : HermLB p) (s : X.functionField), IsAmpleLB P.A.B → s ∈ P.H 0 1 → s ≠ 0 →
    ∃ c₁ : ℕ, ∀ c, c₁ ≤ c → 0 < c → ∃ u₀ : ℝ, ∀ u, u₀ ≤ u → Le (((shiftA P u).A.pow c).dual) N := by
  intro k _ X _ p D hX P N s hA hs hs0
  obtain ⟨rN, hrN⟩ := exists_isRatSec N.isLB
  let Q : Pair p := ⟨N, P.A, rN, P.r', hrN, P.hr'⟩
  obtain ⟨c₁, g, _, hg0, hg, -⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX Q hA 1 Empty (fun e => e.elim)
  refine ⟨c₁, fun c hc hc0 => ?_⟩
  have hsQ : s ∈ Q.H 0 1 := mem_regular_sections_second_bundle_indep_first P N rN hrN hs
  obtain ⟨hpow, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 s hsQ (c - c₁)
  obtain ⟨hf, -⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q 1 c₁ _ _ g (s ^ (c - c₁)) hg hpow
  have e1 : (1 : ℤ) + ((c - c₁ : ℕ) : ℤ) * 0 = 1 := by ring
  have e2 : (c₁ : ℤ) + ((c - c₁ : ℕ) : ℤ) * 1 = c := by push_cast [Nat.cast_sub hc]; ring
  rw [e1, e2] at hf
  obtain ⟨w, _, hw⟩ := GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 c _ hf
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc0
  refine ⟨w / c, fun u hu => ?_⟩
  obtain ⟨-, hBl, -⟩ := GlobalTheory.T.shiftSecondBundleNormPair_norm_ball_generation k X p Q u
  have hwu : w ≤ (c : ℤ) * u := by
    have := (div_le_iff₀ hcpos).1 hu
    push_cast; linarith
  have hmem : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl 1 c 1 := by
    rw [hBl, one_mul]
    exact ⟨hw.1, fun σ y => (hw.2 σ y).trans (Real.exp_le_exp.2 hwu)⟩
  have hne : g * s ^ (c - c₁) ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ hs0)
  have hrepN := (Pair.rep_base k X p (shiftA Q u)).1
  have hrepA := (Pair.rep_base k X p (shiftA Q u)).2.1
  have hpowA := Pair.rep_pow k X p (shiftA Q u) 0 1 _ c hrepA
  have hdual := Pair.rep_dual k X p (shiftA Q u) _ _ _ hpowA
  have e3 : (1 : ℤ) - -((c : ℤ) * 0) = 1 := by ring
  have e4 : (0 : ℤ) - -((c : ℤ) * 1) = c := by ring
  have hmem' : g * s ^ (c - c₁) ∈ (shiftA Q u).Bl (1 - -((c : ℤ) * 0)) (0 - -((c : ℤ) * 1)) 1 := by
    rw [e3, e4]; exact hmem
  exact GlobalTheory.T.hermLBLeBySmallSection_of_rep k X p (shiftA Q u) 1 0 _ _ N _ _ hrepN hdual hne hmem'

end GlobalTheory.HSNef.TwistSmall
