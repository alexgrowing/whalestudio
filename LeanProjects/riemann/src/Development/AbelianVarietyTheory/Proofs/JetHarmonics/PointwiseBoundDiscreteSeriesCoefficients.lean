import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityAtPlaceOfSubadditive
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesKFiniteCoeffCapelliEigenDecayStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundCapelliEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefficientExpansionBoundBallStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HcParamSubIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InterlaceHalf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MarginArithClosing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumOfStdHyp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliParamMemIntAddHalf
open BpJoin Formalism.FourierDecayAlt

namespace GlobalTheory.BpDiscreteSeriesTwoInputs

theorem thmBpAt_mono {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {b C C' : ℝ} {n₀ p₀ : ℕ}
    (hb : 1 ≤ b) (hC : C ≤ C') (h : TBB.ThmBpAt p f b C n₀ p₀) : TBB.ThmBpAt p f b C' n₀ p₀ := by
  intro γ hγ hG
  refine (h γ hγ hG).trans ?_
  gcongr

theorem pointwise_bound_discreteSeries : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ThmBpDS := by
  intro hXi hP Ch C₀ hC₀
  have hC : 0 ≤ 2 * |Ch| := by positivity
  obtain ⟨C₄, Cc, heig⟩ := GlobalTheory.T.pointwiseBound_capelli_eigenfunction hXi hP (2 * |Ch|) (2 * |Ch| / 2 + 6) C₀ hC (by positivity) hC₀
  obtain ⟨G₁, hnum⟩ := GlobalTheory.BpStdNum.num_of_stdHyp (C₀ + 10) (by positivity)
  obtain ⟨G₂, hgrid⟩ := GlobalTheory.StdGrid.std_grid
  obtain ⟨G₃, -, hmar⟩ := GlobalTheory.margin_arith_closing Cc C₀ hC₀
  refine ⟨max C₄ 0, max G₁ (max G₂ G₃), le_max_right _ _, ?_⟩
  intro Cg hCg P Wp Wq _ _ _ _ _ _ p lam lam' ka b n₀ p₀ R f hstd hgaps hDS hf hn1 hn2 hp1 hp2
  have hG₁ : G₁ ≤ Cg := (le_max_left _ _).trans hCg
  have hG₂ : G₂ ≤ Cg := ((le_max_left _ _).trans (le_max_right _ _)).trans hCg
  have hG₃ : G₃ ≤ Cg := ((le_max_right _ _).trans (le_max_right _ _)).trans hCg
  have hk : 2 ≤ P.k := p.hl.2.2
  obtain ⟨hOK, hz, hz', hT, hT', hty, hty'⟩ := p.hP
  have hka : 0 < ka := hstd.2.2.2.1
  have hkp : 0 < (1 / ka) ^ (2 * P.r) := by positivity
  have hT0 : 0 < P.T := (mul_pos_iff_of_pos_right hkp).1 (lt_of_lt_of_le one_pos hstd.2.2.2.2.2.2.1)
  have hT0' : 0 < P.T' := (mul_pos_iff_of_pos_right hkp).1 (lt_of_lt_of_le one_pos hstd.2.2.2.2.2.2.2.1)
  have hint : ∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧
      ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2 := fun i hi =>
    ⟨GlobalTheory.capelliParam_mem_int_add_half P.k P.r Wp _ _ P.u hz (hT ▸ hT0) hty i hi,
      GlobalTheory.capelliParam_mem_int_add_half P.k P.r Wq _ _ P.u' hz' (hT' ▸ hT0') hty' i hi⟩
  obtain ⟨ν₀, hν, hn, habs⟩ := GlobalTheory.hcParam_sub_integral _ lam lam' hstd.1 hDS.1
  set d := Formalism.MainNotions.S.ThB.l1 lam' lam with hd
  have hd0 : 0 ≤ d := by rw [← hn]; positivity
  obtain ⟨hSN, hTb, hTb', hcases⟩ := hgrid Ch Cg hG₂ P lam ka b (200 * d) hk hstd hint hgaps
  have hn₀ : n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 := by
    by_cases h : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i
    · exact (hn1 h).le
    · rw [hn2 h]; exact Nat.zero_le _
  have hq : ((BranchingSupport.n1 ν₀ + (P.r + 1) * (2 * p₀ + n₀) + (P.r + 1) * (P.r + 2) : ℕ) : ℝ) ≤
      d + (C₀ + 10) * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 := by
    have := (hmar Cg hG₃ P.k P.r n₀ p₀ _ d (by omega) hn₀ hp2 le_rfl hd0).2.2
    rw [add_assoc, Nat.cast_add, hn]
    linarith
  obtain ⟨bv, ga, h, hN, hN', hh⟩ := hnum Ch Cg hG₁ P lam _ _ ka b d _ hk hstd hint hd0 hgaps hq
  obtain ⟨hm1, hm2, -⟩ := hmar Cg hG₃ P.k P.r n₀ p₀ h d (by omega) hn₀ hp2 hh hd0
  obtain ⟨⟨hb1, hb2, -, -, hgok⟩, hfam⟩ := GlobalTheory.NumFam.num_fam _ _ _ _ _ _ _ _ _ hN
  have hb : 1 ≤ b := by linarith
  have hgap := (hfam ν₀ (by omega)).2.2.1
  rw [← hν] at hgap
  have hE := GlobalTheory.T.discreteSeries_KFinite_coeff_capelli_eigen_decay P.k P.r _ lam' (h / 2) R Wp Wq f hDS hgap hgok hf
  have hexp := GlobalTheory.T.discreteSeries_coefficient_expansion_bound_ball' (2 * |Ch|) hC P Wp Wq p lam b bv ga h _ (2 * p₀ + n₀) ν₀ R f
    hN hN' hTb hTb' le_rfl (hν ▸ hDS) hf
  have hreg := Formalism.FourierDecayAlt.P.regularity_at_place p f b _ _ (by linarith) hexp
  refine thmBpAt_mono hb (le_max_left _ _) ?_
  exact heig P Wp Wq p f b _ _ n₀ p₀ lam lam' hSN (hcases n₀ hn1 hn2) hp1 hp2 hE hm1
    (fun s => by linarith [habs s]) hreg

end GlobalTheory.BpDiscreteSeriesTwoInputs
