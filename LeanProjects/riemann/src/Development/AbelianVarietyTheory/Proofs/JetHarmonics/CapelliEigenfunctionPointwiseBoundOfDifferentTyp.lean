import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HerGenC
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WithRightAction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.AmapsShExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositiveStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenfunctionBoundThreePlacesStatement

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes

theorem decay_le (c₃ Cc r n N A e : ℝ) (hc : c₃ ≤ Cc) (h0 : 0 ≤ Cc) (hr : 0 ≤ r) (hn : r + 1 ≤ n) (hN : 0 ≤ N)
    (he : 0 ≤ e) (h : Cc * (r + 1) ^ 4 * (N * n ^ 2 + n ^ 3) ≤ A - e) :
    c₃ * (r + 1) ^ 2 * (r * n + 1) ≤ A := by
  have h1 : (1 : ℝ) ≤ r + 1 := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have h2 : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
  have h3 : r * n + 1 ≤ N * n ^ 2 + n ^ 3 := by
    have a1 : r * n + 1 ≤ n ^ 2 := by nlinarith
    have a2 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
    have a3 : 0 ≤ N * n ^ 2 := by positivity
    linarith
  have h4 : 0 ≤ r * n + 1 := by positivity
  calc c₃ * (r + 1) ^ 2 * (r * n + 1) ≤ Cc * (r + 1) ^ 2 * (r * n + 1) := by gcongr
    _ ≤ Cc * (r + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr
    _ ≤ A := by linarith

theorem thmBp_eigen_different_types : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → NFTopDomAll → ∀ C C₃ C₀ : ℝ, 0 ≤ C → 0 ≤ C₃ → 0 ≤ C₀ → ∃ C₄ Cc : ℝ, ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b c A₀ : ℝ) (n₀ p₀ : ℕ) (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ), StdNum C b c P lam → (n₀ = 0 ∧ ∃ l ∈ Finset.Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) → 3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * ((P.r : ℝ) + 1) ^ 2 → EigDec f A₀ lam' → Cc * ((P.r : ℝ) + 1) ^ 4 * (((3 * (P.r + 1) : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ - (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) → (∀ s, |lam' s - lam s| + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c - 1) → TBB.RegularityBoundBigCell p f b C₃ (2 * p₀ + n₀) → TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  intro hX hP5 hNF C C₃ C₀ hC hC₃ hC₀
  obtain ⟨Cb, -, hsh⟩ := GlobalTheory.WithRightAction.exists_place_other_right_type
  obtain ⟨c₃, hA⟩ := GlobalTheory.WigSh.amapsShExists
  obtain ⟨C₄, Cc, hreg⟩ := GlobalTheory.T.capelli_eigenfunction_bound_three_places hX hP5 hNF Cb C₃ (7 + C) C₀ hC₃ (by linarith) hC₀
  refine ⟨C₄, max (max Cc c₃) 0, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b c A₀ n₀ p₀ lam lam' hS hcase hN hp₀ hE hdec hlam h92
  obtain ⟨rfl, l, hl, hgap⟩ := hcase
  have hl' := Finset.mem_Icc.1 hl
  obtain ⟨q, hq0, hz, hz', hπ, hπ', hν, hm, hD⟩ :=
    hsh P Wp Wq Wq p P.u P.u' p.T.base.π' l p.hP hl'.1 hl'.2
  have hG := hS.1 l hl
  have hc1 : 1 ≤ c := hG.1
  have hcb : c + 2 ≤ b := hG.2.1
  have hk : 2 ≤ P.k := p.hl.2.2
  have hposition : 2 * ((0 : ℕ) : ℝ) + 1 ≤ P.u' 1 - P.u' (1 + 1) := by
    have hg := p.hP.1.gap 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
    unfold M.Par.lo M.Par.hi at hg
    have a1 := le_max_right (P.u (1 + 1)) (P.u' (1 + 1))
    have a2 := min_le_right (P.u 1) (P.u' 1)
    push_cast
    linarith
  obtain ⟨Ap, Am, ApPt, AmPt, hAp, hAm, -, hmaps⟩ :=
    hA P Wp Wq Wq Wq P.u P.u' P.u P.u' p q q 1 0 b hz hz' hz hz' (fun h _ => congrFun hπ h) (fun h _ => congrFun hπ h)
      hν hm hν hm le_rfl (by omega) hposition (fun i hi => (hS.1 i hi).2.2.2.2.1) (by push_cast; linarith) (by linarith)
      (fun i _ => by simp) (fun i _ => by simp)
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
  have hm1 := hmaps A₀ f (by
    have := decay_le c₃ _ P.r (2 * (P.r : ℝ) + P.k + 1) _ A₀ _ ((le_max_right Cc c₃).trans (le_max_left _ 0))
      (le_max_right _ _) hr0 (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hdec
    push_cast
    exact this) (hE.2.1 1)
  obtain ⟨hpos, hone, Y, hW, hL⟩ := GlobalTheory.T.grids_at_place_longCut_normaliserPositive C b c (shP P P.u P.u') Wp Wq q lam hC
    (by subst hq0; exact hG) (by subst hq0; exact hgap)
  refine hreg P Wp Wq Wq Wq P.u P.u' P.u P.u' p q q f Ap Am ApPt AmPt b
    (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) A₀ 0 p₀ (0 * (P.r + 1)) (Pst lam c) (Pst lam c) Y Y 3 (3 * (P.r + 1))
    (by linarith) hone le_rfl (Nat.zero_le _) hp₀ hz hz' hz hz' le_rfl (by omega) hpos hpos hD hD hE.1 hE.2.1
    hAp hAm ?_ hm1 h92 hW hL hW hL hN lam lam' c hE.2.2 ?_ hlam (fun y => le_rfl) (fun y => le_rfl)
  · have hle : Cc ≤ max (max Cc c₃) 0 := (le_max_left Cc c₃).trans (le_max_left _ 0)
    refine le_trans ?_ (hdec.trans (le_of_eq ?_))
    · gcongr
    · push_cast; ring
  · intro s t hst
    have hd := hG.2.2.2.2.2.2.1
    rcases lt_or_gt_of_ne hst with h | h
    · have := hd s t h
      exact le_trans (by linarith) (le_abs_self _)
    · have := hd t s h
      exact le_trans (by linarith) (neg_le_abs _)

end GlobalTheory.capelliEigenfunction_pointwiseBound_of_differentTypes
