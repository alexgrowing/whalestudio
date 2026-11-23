import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptManual
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCptCopy

namespace Formalism.FourierDecayAlt.P.TBBx3
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem _root_.Formalism.FourierDecayAlt.P.TBBx3.head_continuity_at_zero_of_standardCpt (hPS : KB.PStdCpt) (hTP : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) : TBB.HeadContinuityAtZero p nn F Y N := by
  intro j hj h hh w hw hN
  obtain ⟨φ, hφc, hφi, hφ, -⟩ := hPS hTP Wp Wq P p F j hj w h h hh hh Cb hCb hF hw.1
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hAdef
  refine ⟨fun c => ((A / TBB.normC nn w : ℝ) : ℂ) * φ c, continuous_const.mul hφc, hφi.const_mul _, ?_⟩
  intro c hc
  simp only
  rw [hφ c hc]
  have hA : 0 ≤ A := Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le P.k P.r 0 (fun _ _ => 1) (fun _ _ => one_pos) h 1 le_rfl
    (by rw [hh.2]; omega)
  have hn : TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(1, c)]) =
      A * C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] := by
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hh.2, hAdef,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) h 1 le_rfl (by rw [hh.2]; omega)]
  unfold TBB.NP
  rw [hn]
  by_cases hjr : j = P.r
  · subst hjr
    by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
    · have h0 : p.RR F (P.r + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) = 0 :=
        Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w h _ c hh.2 hc2
      rw [h0]
      simp
    · push Not at hc2
      have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
      have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
      have hlast : D.ptGG (TBB.TTp p) (h ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
        simp [D.ptGG, D.ptLast]
      have hTT : TBB.TTp p = P.T * P.T' := by
        unfold TBB.TTp
        rw [hT, hT']
      have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
          KB.levW P (P.r + 1) c := by
        rw [hlast, hTT]
        rw [hT, hT'] at hc2
        simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
        rw [if_pos ⟨by omega, trivial⟩]
        simp
      have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
        rw [← hfac, hlast]
        simp only [C.nAux]
        rw [if_pos ⟨by omega, trivial⟩]
        have : 0 ≤ Complex.normSq c - TBB.TTp p := by
          unfold TBB.TTp; linarith
        simpa using pow_nonneg this _
      rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
      push_cast
      ring
  · have hfac : C.nAux P.k P.r (D.ptGG (TBB.TTp p) (h ++ [(1, c)])) (fun _ _ => 1) (1 + j) [(1, c)] =
        KB.levW P (j + 1) c := by
      simp only [C.nAux, KB.levW]
      rw [if_neg (by omega), if_neg (by omega)]
      have e : 1 + j + 1 - 1 = j + 1 := by omega
      rw [e]
      simp only [one_mul, mul_one, Nat.cast_one]
      congr 1
      ring
    have hlev : 0 ≤ KB.levW P (j + 1) c := by
      simp only [KB.levW]
      rw [if_neg (by omega)]
      exact zpow_nonneg (norm_nonneg _) _
    rw [hfac, Real.mul_self_sqrt (mul_nonneg hA hlev)]
    push_cast
    ring

end
end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem _root_.Formalism.FourierDecayAlt.P.head_continuity_at_zero_of_compact_coefficientsCpt (hPS : KB.PStdCpt) (hTP : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) :
    Formalism.FourierDecayAlt.TBB.HeadContinuityAtZero p nn F Y N := by
  exact TBBx3.head_continuity_at_zero_of_standardCpt hPS hTP p nn F Y N Cb hCb hF

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limPos_of_limEvTCpt (hA : P5.ThmPActualCpt) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimPos p F Y N := by
  obtain ⟨Cc, hCc⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ A N Y hDD hχ hF hFA hth hEv w hw hN
  have hcut : ∀ ε : ℝ, 0 < ε → 0 ≤ (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re := by
    intro ε hε
    obtain ⟨hcpt, hlim⟩ := hCc Wp Wq P p F χ ε A N (cutN P.k P.r) hDD hχ hε hF hFA hth (fun _ _ => rfl)
    have hT := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    exact ge_of_tendsto hT (Eventually.of_forall fun n => truncated_limit_positivity_holdsCpt hA p (hcpt n) Y N w hw hN)
  exact ge_of_tendsto (hEv w hw hN) (eventually_nhdsWithin_of_forall fun ε hε => hcut ε hε)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limE_of_limEvTCpt (hA : P5.ThmPActualCpt) (Cb : ℝ) : ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ nn : ℝ → ℝ)
    (A : ℝ) (N : ℕ) (Y : Finset ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → (∀ y, 0 ≤ nn y) → B.CkOn ⊤ (B.GV P.k P.r) F →
    (∀ m : ℕ, B.InCC A m F) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    LimEvT p χ F Y N → LimBd p nn F Y N → LimE p nn χ F Y N := by
  obtain ⟨Cc, hC⟩ := limPos_of_limEvTCpt hA Cb
  refine ⟨Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F χ nn A N Y h1 h2 h3 h4 h5 h6 hEv hBd
  exact limE_of_partsT p nn χ F Y N h3 hEv (hC Wp Wq P p F χ A N Y h1 h2 h4 h5 h6 hEv) hBd

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.TBBx5.integral_four_of_parts_holdsCpt : IntegralFourFromComponentsCpt := by
  intro hA hSS hDL hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hF hnn hgrid
  exact integral_four_at_place_of_partsCpt hA hSS hDL p nn F Y Λ K N (formNonneg_ofCpt hA hFP p) hF hnn hgrid

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.integral_four_at_placeCpt (hA : P5.ThmPActualCpt) (hSS : KB.SizeStdCpt) (hDL : KB.DegLift) (hFP : PBL.FormPosCpt)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y) (hgrid : TBBx5.LiftGrid p nn Y Λ K N) :
    Formalism.FourierDecayAlt.TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N := TBBx5.integral_four_of_parts_holdsCpt hA hSS hDL hFP Wp Wq P p nn F Y Λ K N hF hnn hgrid

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.TBBx5
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.TBBx5.integral_three_of_parts_holdsCpt : CurvatureIntegralOfPartsCpt := by
  intro hA hPS hVI hSS hDW hFP Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N Cb hCb hF hnn hgrid
  exact integral_three_at_place_of_partsCpt hA hPS hVI hSS hDW p nn F Y Λ K N Cb hCb (formNonneg_ofCpt hA hFP p) hF hnn hgrid

end Formalism.FourierDecayAlt.P.TBBx5

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.integral_three_at_placeCpt (hA : P5.ThmPActualCpt) (hPS : KB.PStdCpt) (hVI : KB.VIsoCpt) (hSS : KB.SizeStdCpt)
    (hDW : KB.DegWave) (hFP : PBL.FormPosCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ)
    (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hnn : ∀ y, 0 < nn y)
    (hgrid : TBBx5.WaveGrid p nn Y Λ K N) : Formalism.FourierDecayAlt.TBB.KernelFourierIntegralBound p nn F Y Λ K N := TBBx5.integral_three_of_parts_holdsCpt hA hPS hVI hSS hDW hFP Wp Wq P p nn F Y Λ K N Cb hCb hF hnn hgrid

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
section place
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.corS_of_cptCpt (hA : P5.ThmPActualCpt) (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ) (Cb C₂ : ℝ)
    (hLS : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (Λ : ℝ) (K N : ℕ), 3 ≤ K → 1 ≤ Λ →
      TBB.PosAt p nn F Y N → TBB.HeadContinuityAtZero p nn F Y N → TBB.KernelFourierIntegralBound p nn F Y Λ K N → TBB.KernelArgumentHypothesisScalar p nn F Y Λ K N →
      TBB.BlockGrowthBound p nn F Y K N → TBB.LemmaS p nn F Y Λ K N C₂)
    (hC₂ : 0 ≤ C₂) (hK : 3 ≤ K) (hKN : (P.r + 1) * K ≤ N) (hΛ : 1 ≤ Λ) (hnn : ∀ y, 0 < nn y)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G)
    (hWG : TBBx5.WaveGrid p nn Y Λ K N) (hLG : TBBx5.LiftGrid p nn Y Λ K N) (hI5 : TBB.BlockGrowthBound p nn G Y K N) :
    TBB.CorS p nn G Y Λ K N C₂ := by
  have hPS : KB.PStdCpt := Formalism.FourierDecayAlt.P.standard_pairing_of_headsCpt Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  have hPos : TBB.PosAt p nn G Y N := posAt_of_cptCpt hA p nn G Y N (fun y => (hnn y).le) hG
  have hI2 := Formalism.FourierDecayAlt.P.head_continuity_at_zero_of_compact_coefficientsCpt hPS hA p nn G Y N Cb hCb hG
  have hI3 := Formalism.FourierDecayAlt.P.integral_three_at_placeCpt hA hPS Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support Formalism.FourierDecayAlt.P.size_standard_compact
    Formalism.FourierDecayAlt.P.degree_of_plane_wave (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p nn G Y Λ K N Cb hCb hG hnn hWG
  have hI4 := Formalism.FourierDecayAlt.P.integral_four_at_placeCpt hA Formalism.FourierDecayAlt.P.size_standard_compact Formalism.FourierDecayAlt.P.degree_of_lift_pairing
    (Formalism.FourierDecayAlt.P.module_form_pos_compact_support : PBL.FormPosCpt) p nn G Y Λ K N hG hnn hLG
  exact Formalism.FourierDecayAlt.P.corSOfLemmaS_statement Wp Wq P p nn G Y Λ K N C₂ hKN hC₂ hPos
    (hLS Wp Wq P p nn G Y Λ K N hK hΛ hPos hI2 hI3 hI4 hI5)

end place
end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.ptBound_dec_allCpt (hA : P5.ThmPActualCpt) : ∃ C₂ : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ κ₀ : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ),
      1 ≤ Λ → 0 < κ₀ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) F →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ F ε)) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ F ε) Y N) →
      LimE p nn χ F Y N → LemB p F κ₀ → TBB.PtBound p F (κ₀ * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hLS⟩ :=
    Formalism.FourierDecayAlt.Final.tbb_lemmaSOfSteps Formalism.FourierDecayAlt.Final.tbb_stepOne Formalism.FourierDecayAlt.Final.tbb_stepUp
  refine ⟨C₂, hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p F Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb hF hWG hLG hI5 hT hZ hE hB
  refine Formalism.FourierDecayAlt.Final.tbb_ptBoundOfCorS Wp Wq P p nn χ F Y Λ K N C₂ κ₀ hC₂.le hκ hnn
    ⟨1, one_pos, fun ε hε _ => ?_⟩ (TBBx3.vecCutAt_of_one p χ F hχ.2.2)
    (TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB)
  refine corS_of_apx p nn _ Y Λ K N C₂ (fun n => ?_) (hT ε hε) (hZ ε hε)
  exact corS_of_cptCpt hA p nn _ Y Λ K N Cb C₂ hLS hC₂.le hK hKN hΛ hnn hCb
    (cptCoef_apx P p.T.base hχ hF hε n) hWG hLG (hI5 ε hε n)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_of_leaves_decCpt (hA : P5.ThmPActualCpt) (C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
      (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b Λ κ₀ : ℝ) (n₀ p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ)
      (Cb : ℝ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f →
      B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      Amaps p f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε) n) Y K N) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε)) →
      (∀ ε : ℝ, 0 < ε → LimTopN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε)) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Ap p₀) ε) Y N) →
      (∀ ε : ℝ, 0 < ε → LimZeroN p nn (D.cutF p.T.base χ (TBBx4.fpm p f Am p₀) ε) Y N) →
      LimE p nn χ (TBBx4.fpm p f Ap p₀) Y N → LimE p nn χ (TBBx4.fpm p f Am p₀) Y N →
      LemB p (TBBx4.fpm p f Ap p₀) κ₀ → LemB p (TBBx4.fpm p f Am p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, hC₂, hPB⟩ := ptBound_dec_allCpt hA
  obtain ⟨C₄, hC₄⟩ := Formalism.FourierDecayAlt.Final.tbb_thmBpOfParts C₃ CΛ C₀ C₂ Cκ hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f Ap Am ApPt AmPt b Λ κ₀ n₀ p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hTq hn₀
    hp₀ hK hKN hχ hnn hCb hf hAp hAm hAm' hExp hWG hLG hI5p hI5m hTp hTm hZp hZm hEp hEm hBp hBm
  obtain ⟨h1, h2, h3, h4, h5⟩ := hAm'
  exact hC₄ Wp Wq P p f (TBBx4.fpm p f Ap p₀) (TBBx4.fpm p f Am p₀) b Λ κ₀ n₀ p₀ hb hΛ hΛb hκ hκb
    hTq hn₀ hp₀ (TBBx4.normAt_fpm p f Ap Am ApPt AmPt b n₀ p₀ h1 h2 h3 h4 h5)
    (hPB Wp Wq P p _ Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb (ckOn_fpm p p₀ hf hAp) hWG hLG
      hI5p hTp hZp hEp hBp)
    (hPB Wp Wq P p _ Λ κ₀ χ nn Y K N Cb hΛ hκ hK hKN hχ hnn hCb (ckOn_fpm p p₀ hf hAm) hWG hLG
      hI5m hTm hZm hEm hBm)
    (TBBx4.regularity_at_place_of_expansion p f b C₃ (2 * p₀ + n₀) (by linarith) hExp)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_mainCpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ κ₀ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      LemB p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, hC₄⟩ := thmBpAt_of_leaves_decCpt hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ κ₀ A₀ p₀ χ nn Y K N hb hΛ hΛb hκ hκb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2
    hexp hWG hLG hI5 hE hB
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hFd := inCC_fpm_id p p₀ hfA
  have hFck := ckOn_fpm p p₀ hf hid
  have hTN : ∀ ε : ℝ, 0 < ε → LimTopN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) :=
    hc₃ Wp Wq P p nn χ _ _ hth1 hχ hFd hFck
  have hZN : ∀ ε : ℝ, 0 < ε → LimZeroN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) Y N :=
    fun ε hε => hCc Wp Wq P p _ χ ε _ N nn Y hCb hχ hε hFck hFd hth2
  exact hC₄ Wp Wq P p f _ _ _ _ b Λ κ₀ 0 p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hT (Nat.zero_le _) hp₀ hK hKN hχ hnn
    hCb hf hid hid (amaps_id p f b) hexp hWG hLG hI5 hI5 hTN hTN hZN hZN hE hE hB hB

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main1Cpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, h⟩ := thmBpAt_mainCpt hA Cb C₃ CΛ C₀ 0 hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE
  exact h Wp Wq P p f b Λ 1 A₀ p₀ χ nn Y K N h1 h2 h3 one_pos (by simp) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE (lemB_one p _)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main2Cpt (hA : P5.ThmPActualCpt) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, h⟩ := thmBpAt_main1Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cc', hL⟩ := limE_of_limEvTCpt hA Cb
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    h16 h17 h18 h19 hEv hBd
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) :=
    fun _ _ => ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, Set.mem_univ _,
      contDiffOn_const, fun _ _ _ => rfl⟩
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16 h17 h18 h19
    (hL Wp Wq P p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) χ nn
      (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N Y h10 h8 (fun y => (h9 y).le) (ckOn_fpm p p₀ h11 hid)
      (inCC_fpm_id p p₀ h12) h15 hEv hBd)

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.GT.top_level_fibreCpt : FibreTopCpt := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw a a' ha ha'
  have hPS : KB.PStdCpt := Formalism.FourierDecayAlt.P.standard_pairing_of_headsCpt Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  set κ : ℝ := √A * √A' / TBB.normC nn w with hκ
  constructor
  · obtain ⟨φ, -, hφi, hφ, -⟩ := hPS hA Wp Wq P p F P.r le_rfl w a a ha ha Cb hCb hF hw
    refine (hφi.const_mul ((√A * √A / TBB.normC nn w : ℝ) : ℂ)).congr ?_
    filter_upwards [PBL.ae_ne_zero_complex] with c hc
    rw [← np_top_two p nn F a a ha ha w c, hφ c hc]
  · obtain ⟨φ, -, -, hφ, hφs⟩ := hPS hA Wp Wq P p F P.r le_rfl w a a' ha ha' Cb hCb hF hw
    have h0 := hφs 0
    simp only [PBASM.waveG_zero_eq_self] at h0
    have hf0 : ∀ c : ℂ, P5.fsv 0 c = 1 := fun c => by simp [P5.fsv]
    simp only [hf0, one_mul] at h0
    rw [TBBx5.li_np p nn F P.r le_rfl w a a' ha ha', TBBx5.wv_nPt p P.r le_rfl a ha,
      TBBx5.wv_nPt p P.r le_rfl a' ha', ← h0, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [PBL.ae_ne_zero_complex] with c hc
    rw [← np_top_two p nn F a a' ha ha' w c, hφ c hc]

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.limEvT_fpm_of_NFCpt (hA : P5.ThmPActualCpt) (h1 : NFTopFormAllCpt) (h2 : NFTopPtwAll) (h3 : NFTopDomAll) (h4 : NFTopIdAll) (Cb : ℝ) :
    ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N →
      LimEvT p χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N := by
  obtain ⟨C1, k1⟩ := h1 hA Cb
  obtain ⟨C2, k2⟩ := h2 Cb
  obtain ⟨C3, k3⟩ := h3 Cb
  obtain ⟨C4, k4⟩ := h4 Cb
  refine ⟨max (max C1 C2) (max C3 C4), ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH
  have mono : ∀ C, C ≤ max (max C1 C2) (max C3 C4) → NFHyp Cb C p f A₀ p₀ χ N := by
    intro C hC
    unfold NFHyp at hH ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
    refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
    gcongr
  exact limEvT_of_NF p χ _ Y N (k1 Wp Wq P p f A₀ p₀ χ Y N (mono C1 (by simp))) (k2 Wp Wq P p f A₀ p₀ χ Y N (mono C2 (by simp)))
    (k3 Wp Wq P p f A₀ p₀ χ Y N (mono C3 (by simp))) (k4 Wp Wq P p f A₀ p₀ χ Y N (mono C4 (by simp)))

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.thmBpAt_main4Cpt (hA : P5.ThmPActualCpt) (h1 : NFTopFormAllCpt) (h2 : NFTopPtwAll) (h3 : NFTopDomAll)
    (h4 : NFTopIdAll) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimBd p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_main2Cpt hA Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NFCpt hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3
    hth4 hN2 hexp hWG hLG hI5 hBd
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2 hth3 hexp hWG hLG
    hI5 (hn Wp Wq P p f A₀ p₀ χ Y N ⟨hχ, hCb, hf, hfA, hth4, hN2⟩) hBd

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
open GLG in

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.low_level_germCpt : GLGermCpt := by
  intro _hA Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _hCb hF hnn b s hb hs hbs h hh w _hw _hN H _ _ _ Vec hVec K hK hK0
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have hF0 := hF
  obtain ⟨hCk, hsupp, δ, hδ, hG⟩ := hF
  have heq : ∀ g ∈ B.GV P.k P.r, D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ g = F g :=
    cutF_eq_on_gv p.T.base Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hG hδ le_rfl
  have hRR : ∀ a a', p.RR F (b + (m + 2) - 1) w a a' =
      p.RR (D.cutF p.T.base Formalism.FourierDecayAlt.P.Topx2.chi0 F δ) (b + (m + 2) - 1) w a a' :=
    fun a a' => rr_congr_belowG p hF0 (fun g hg => (heq g hg).symm) _ hbs (by omega) w a a'
  have hsz : D.ptSize h + (m + 2) = b + (m + 2) - 1 := by rw [hh.2]; omega
  have hloc : D.IsLocPt h (D.ptSize h) := ⟨hh.1, rfl⟩
  obtain ⟨V, i1, i2, i3, Bf, Φ, Cp, Cst, hCp, hBf, hker, hgerm⟩ :=
    Formalism.FourierDecayAlt.P.germ_at_place Wp Wq P p.T (M.sgn P p.l0) w F Formalism.FourierDecayAlt.P.Topx2.chi0 δ h m (b + (m + 2) - 1) hbs
      hsz hCk hsupp Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hδ p.hl.2.2 hloc K hK hK0
  set Mv : ℕ := U.Mlev P.k (P.r - (b + (m + 2) - 1)) with hMv
  have hM : 2 ≤ Mv := by rw [hMv]; unfold U.Mlev; omega
  set nH : ℝ := C.nAux P.k P.r 0 (fun _ _ => 1) 1 h with hnH
  have hnH0 : 0 ≤ nH := Formalism.FourierDecayAlt.P.FormNormSumIdentities.weight_product_nonneg P.k P.r (fun _ _ => 1) (fun _ _ => zero_le_one) 1 h
  set μ0 : ℝ := √nH / √(TBB.normC nn w) with hμ0
  refine ⟨Cp * |μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * Cst, fun x hx Dv hDv => ?_⟩
  have hD0 : Dv ≠ 0 := fun e => hK0 (e ▸ hDv)
  rw [lhs_eq_sum]
  have hy := np_PP p nn hnn F _ w b m hb hbs hRR h hh hsz Bf Φ K hker x Dv hx hDv hD0
  have hle := Formalism.FourierDecayAlt.P.FormNormSumIdentities.norm_sum_le_of_form (TBB.NP p nn F (b + (m + 2) - 1) w) Vec hVec Bf Cp hCp hBf
    (Finset.insertNone (G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv))) (aC m x) (PP m h x Dv)
    (fun j => ((lam p nn w (PP m h x Dv j) : ℝ) : ℂ) • FormNormSumIdentities.yG U.betaU m Φ (qG m x Dv j)) hy
  have hl1 : lam p nn w (PP m h x Dv none) =
      μ0 * ((‖x⁻¹‖ ^ ((m + 1) * (Mv + m))) * ‖x ^ (m + 1) * Dv‖ ^ (Mv - 2)) := by
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)])) / √(TBB.normC nn w) = _
    rw [nPt_block (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, ← mul_pow, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hl2 : ∀ z ∈ G.rootSet (m + 2) ((-1) ^ (m + 3) * Dv),
      lam p nn w (PP m h x Dv (some z)) = μ0 * ‖z‖ ^ ((m + 2) * (Mv + m - 1)) := by
    intro z _
    show √(TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m + 2, z)])) / √(TBB.normC nn w) = _
    rw [nPt_long (TBB.TTp p) b m hb hbs h hh.2, Real.sqrt_mul hnH0, Real.sqrt_sq (by positivity), hμ0]
    ring
  have hcs := conjSum_TBB m Mv hM Φ x Dv hx hD0 μ0 (fun j => lam p nn w (PP m h x Dv j)) hl1 hl2
  rw [hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hle
  have hg' := hgerm x⁻¹ Dv (inv_ne_zero hx) hDv
  rw [norm_inv] at hg'
  calc _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| *
        ‖U.uD U.betaU m Mv Φ x⁻¹ Dv - U.aD U.betaU m Mv Φ x⁻¹ Dv‖) := hle
    _ ≤ Cp * (|μ0 * Real.pi ^ ((m + 2) * (m + 1) / 2)| * (Cst * ‖x‖⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg' (abs_nonneg _)) hCp
    _ = _ := by ring

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.germDataLowAll_of_partsCpt (hGr : GLGramCpt) (hFi : GLFibreCpt) (hCo : GLContCpt) (hGe : GLGermCpt) : GermDataLowAllCpt := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn b s hb hs hbs hlev h hh w hw hN hBdd
  have hi : b + s - 1 ≤ P.r := hlev
  have hN' : w.length ≤ N := by omega
  obtain ⟨H, i1, i2, i3, Vec, hVec⟩ := hGr hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 1) hi w hw hN'
  let _ := i1; let _ := i2; have _ := i3
  have hs0 : s ≠ 0 := by omega
  have hpi : (0 : ℝ) < Real.pi ^ (s - 1) := pow_pos Real.pi_pos _
  set κ : ℝ := (Real.pi ^ (s - 1))⁻¹ with hκ
  have hκκ : Real.pi ^ (2 * (s - 1)) * (κ * κ) = 1 := by
    rw [hκ, pow_mul', sq, ← mul_inv, mul_inv_cancel₀ (by positivity)]
  let ut : ℂ → ℂ → H := fun x D => (((κ * ‖x‖ ^ (s - 1)) : ℝ) : ℂ) • Vec (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])
  let bt : ℂ → H := fun z => if z = 0 then 0 else ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])

  have hcv : ∀ x : ℂ, x ≠ 0 → ∀ c : ℂ, PBK.cvec s ut x c = (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := by
    intro x hx c
    have ha : x ^ (s - 1) ≠ 0 := pow_ne_zero _ hx
    have hn : (‖x‖ ^ (s - 1) : ℝ) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    simp only [PBK.cvec, ut, smul_smul, List.append_assoc, List.cons_append, List.nil_append]
    rw [mul_div_cancel₀ c ha, ← Complex.ofReal_mul]
    congr 2
    field_simp

  have hj : b + s - 2 + 1 = b + s - 1 := by omega
  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) (b + s - 2) := by
    intro t ht
    have := gl_isLocPt_snoc hh (by omega : 1 ≤ s - 1) ht
    rwa [show b - 1 + (s - 1) = b + s - 2 by omega] at this

  have hgram : ∀ x x' : ℂ, x ≠ 0 → x' ≠ 0 →
      ∫ c, ⟪PBK.cvec s ut x c, PBK.cvec s ut x' c⟫_ℂ =
        ((κ * κ : ℝ) : ℂ) * TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) := by
    intro x x' hx hx'
    obtain ⟨-, hfib⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN'
      (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x'⁻¹)]) (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx'))
    rw [hj] at hfib
    rw [← hfib, ← integral_const_mul]
    congr 1
    funext c
    rw [hcv x hx c, hcv x' hx' c, GermFibreKernels.inner_real_smul_smul, hVec]

  have hbz : ∀ z : ℂ, z ≠ 0 → PBK.bz s bt z = Vec (h ++ [(s, z)]) := by
    intro z hz
    simp only [PBK.bz, bt, if_neg hz, smul_smul, ← Complex.ofReal_mul]
    rw [mul_inv_cancel₀, Complex.ofReal_one, one_smul]
    have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
    have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    positivity

  have hVecR : ∀ i (hi' : i = b + s - 1) a a', TBB.NP p nn F i w a a' = ⟪Vec a, Vec a'⟫_ℂ := by
    intro i hi' a a'; subst hi'; exact hVec a a'
  have hcont1 : ∀ t : ℂ, t ≠ 0 → ContinuousOn (fun c : ℂ => Vec ((h ++ [(s - 1, t)]) ++ [(1, c)])) {0}ᶜ := by
    intro t ht
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) 1 le_rfl (by omega) w hw hN' _ (hloc t ht)
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ hj) (fun c => (h ++ [(s - 1, t)]) ++ [(1, c)]) {0}ᶜ hk
  have hcontS : ContinuousOn (fun z : ℂ => Vec (h ++ [(s, z)])) {0}ᶜ := by
    have hk := hCo hA Wp Wq P p nn F Y N Cb hCb hF hnn (b - 1) s (by omega) (by omega) w hw hN' h hh
    exact GermFibreKernels.vec_continuousOn _ Vec (hVecR _ (by omega)) (fun z => h ++ [(s, z)]) {0}ᶜ hk

  obtain ⟨B0, hB0⟩ := hBdd w (TBBx1.isExt_self hw hN')
  refine ⟨H, i1, i2, i3, ut, bt, -U.betaU, (-1) ^ (s + 1), 1, κ * κ * B0, Real.pi ^ (2 * (s - 1)), 1,
    zero_le_one, ?_, Or.inl rfl, ?_, gl_fsv, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ h1)
  · have hae : ∀ᵐ z : ℂ ∂volume, z ∈ ({0}ᶜ : Set ℂ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton (0 : ℂ))
    have hmeas0 : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
    refine ⟨hs0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold U.betaU Formalism.QuantumDeterminants.cStd
      simp [Complex.I_ne_zero]
    · simp [norm_pow]
    ·
      intro _ _ x hx
      refine (PBK.memLp_cvec s ut x hx).2 ?_
      have hfun : PBK.cvec s ut x = fun c => (κ : ℂ) • Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)]) := funext (hcv x hx)
      rw [hfun]
      refine MemLp.const_smul ?_ _
      have hmeas : AEStronglyMeasurable (fun c : ℂ => Vec ((h ++ [(s - 1, x⁻¹)]) ++ [(1, c)])) volume := by
        have h2 := (hcont1 x⁻¹ (inv_ne_zero hx)).aestronglyMeasurable (μ := volume) hmeas0
        rwa [Measure.restrict_eq_self_of_ae_mem hae] at h2
      refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
      obtain ⟨hint, -⟩ := hFi hA Wp Wq P p nn F Y N Cb hCb hF hnn (b + s - 2) (by omega) w hw hN' _ _
        (hloc _ (inv_ne_zero hx)) (hloc _ (inv_ne_zero hx))
      rw [hj] at hint
      refine (Complex.reCLM.integrable_comp hint).congr (Eventually.of_forall fun c => ?_)
      simp only [Complex.reCLM_apply]
      rw [hVec, gl_inner_self, Complex.ofReal_re]
    ·
      intro _ _ x hx
      have e1 := PBK.cvec_inner s ut ut x x hx hx
      simp only [div_self (pow_ne_zero _ hx), norm_one, Complex.ofReal_one, one_smul, one_mul] at e1
      have e2 : ∫ D, ⟪ut x D, ut x D⟫_ℂ = ((∫ D, ‖ut x D‖ ^ 2 : ℝ) : ℂ) := by
        simp_rw [gl_inner_self]; exact integral_ofReal
      rw [e2, hgram x x hx hx] at e1
      have e3 := congrArg Complex.re e1
      rw [Complex.ofReal_re, Complex.re_ofReal_mul] at e3
      rw [← e3]
      have hE : (TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, x⁻¹)]) (h ++ [(s - 1, x⁻¹)])).re ≤ B0 :=
        hB0 ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      exact mul_le_mul_of_nonneg_left hE (mul_self_nonneg κ)
    ·
      intro _ _
      let _ : MeasurableSpace H := borel H
      have _ : BorelSpace H := ⟨rfl⟩
      let g : ℂ → H := fun z => ((((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • Vec (h ++ [(s, z)])
      have hgc : ContinuousOn g {0}ᶜ := by
        refine ContinuousOn.smul ?_ hcontS
        refine Complex.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.inv₀ (Continuous.continuousOn (by fun_prop)) fun z hz => ?_
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      have hbt' : bt = ({0}ᶜ : Set ℂ).piecewise g (fun _ => 0) := by
        funext z
        by_cases hz : z = 0
        · simp [bt, hz]
        · simp [bt, hz, Set.piecewise, g]
      show StronglyMeasurable bt
      rw [stronglyMeasurable_iff_measurable_separable, hbt']
      refine ⟨ContinuousOn.measurable_piecewise hgc continuousOn_const hmeas0, ?_⟩
      refine TopologicalSpace.IsSeparable.mono (s := g '' {0}ᶜ ∪ {0}) ?_ (Set.range_subset_iff.2 fun z => ?_)
      · exact (hgc.isSeparable_image (TopologicalSpace.IsSeparable.of_separableSpace _)).union
          (Set.finite_singleton (0 : H)).isSeparable
      · by_cases hz : z ∈ ({0}ᶜ : Set ℂ)
        · left; rw [Set.piecewise_eq_of_mem _ _ _ hz]; exact ⟨z, hz, rfl⟩
        · right; rw [Set.piecewise_eq_of_notMem _ _ _ hz]; rfl
    ·
      intro _ _ K' hK hK0
      have hsub : K' ⊆ {0}ᶜ := fun z hz hz0 => hK0 (by rw [Set.mem_singleton_iff.1 hz0] at hz; exact hz)
      have hc : ContinuousOn (fun z => ‖Vec (h ++ [(s, z)])‖ ^ 2) K' := (hcontS.norm.pow 2).mono hsub
      refine (hc.congr fun z hz => ?_).integrableOn_compact hK
      rw [hbz z (fun h0 => hK0 (h0 ▸ hz))]
    ·
      intro _ _ K' hK hK0
      obtain ⟨C, hC⟩ := hGe hA Wp Wq P p nn F Y N Cb hCb hF hnn b s hb hs hi h hh w hw hN' H Vec hVec K' hK hK0
      refine ⟨C, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      refine le_of_eq_of_le ?_ (hC x hx D hD)
      congr 2
      unfold PBK.mainD
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by
        rintro rfl
        have hr := (Polynomial.mem_nthRoots (by omega : 0 < s)).1 (Multiset.mem_toFinset.1 hz)
        rw [zero_pow hs0] at hr
        exact hD0 (by simpa using hr.symm)
      exact congrArg (fun v => G.psi (-U.betaU) ((s : ℂ) * z * x) • v) (if_neg hz0)
  · intro t t' ht ht'
    have hg := hgram t⁻¹ t'⁻¹ (inv_ne_zero ht) (inv_ne_zero ht')
    simp only [inv_inv] at hg
    show _ = _ * ‖∫ c, ⟪PBK.cvec s ut t⁻¹ c, PBK.cvec s ut t'⁻¹ c⟫_ℂ‖
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg κ), ← mul_assoc, hκκ,
      one_mul]
  · intro z hz
    unfold TBB.Ew
    rw [hbz z hz, hVec, gl_inner_self, Complex.ofReal_re, one_mul]

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
noncomputable section

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.low_level_continuityCpt : GLContCpt := by
  intro _ Wp Wq _ _ _ _ _ _ P p nn F Y N Cb _ hF _ j m hm hjm w hw _ a ha
  have hsz : D.ptSize a + m = j + m := by rw [ha.2]
  have hRR := rank_below_compact Wp Wq P p F hF (j + m) hjm w hw.1 a a m hm hsz hsz
  have hn := nPt_app_cont (P := P) (TBB.TTp p) a m
  have e1 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_fst (fun cc hcc => hcc.1)
  have e2 : ContinuousOn (fun cc : ℂ × ℂ => TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := hn.comp continuousOn_snd (fun cc hcc => hcc.2)
  have hw' : ContinuousOn (fun cc : ℂ × ℂ => ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.1)])) *
      Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (a ++ [(m, cc.2)])) / TBB.normC nn w : ℝ) : ℂ))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_sqrt.comp_continuousOn e1).mul (Real.continuous_sqrt.comp_continuousOn e2)).div_const _)
  exact hw'.mul hRR

end
end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP.GT
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.GT.germDataTopAll_of_partsCpt (hTG : TopGram1) (hTC : TopCore1) (hFT : FibreTopCpt) (hYC : YCont)
    (hMU : FieldMemU) (hSU : FieldSup) (hME : FieldMeas) (hLO : FieldLoc) : GermDataTopAllCpt := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F Y K N Cb hCb hF hnn
  intro b s hb hs hbs hlev h hh w hw hN hBdd
  have hbs' : b + s = P.r + 2 := by omega
  have hr2 : b + s - 2 = P.r := by omega
  have hr1 : b + s - 1 = P.r + 1 := by omega
  obtain ⟨I, _, c, Fi, L, hc, hFi, hgram⟩ := hTG Wp Wq P p nn F w Cb hCb hF hw.1 hnn
  have hFib := hFT hA Wp Wq P p nn F w Cb hCb hF hw.1
  have hV : VecHyp p nn F w c Fi L :=
    { hc := hc, hFi := hFi, gram := hgram, int := fun a ha => (hFib a a ha ha).1,
      fibre := fun a a' ha ha' => (hFib a a' ha ha').2,
      cont := fun i m h' hh' hm hsz => hYC Wp Wq P p (Fi i) (hFi i) w.length m h' hh' hm hsz }
  obtain ⟨SS, hSS⟩ := hBdd w (TBBx5.isExt_self P p.l0 Y N K w hw (by omega))
  have hs0 : s ≠ 0 := by omega
  have hsz : D.ptSize h = b - 1 := hh.2

  have hloc : ∀ t : ℂ, t ≠ 0 → D.IsLocPt (h ++ [(s - 1, t)]) P.r := by
    intro t ht
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_append.1 hq with hq | hq
      · exact hh.1 q hq
      · simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨by simp only; omega, ht⟩
    · have e : D.ptSize (h ++ [(s - 1, t)]) = D.ptSize h + (s - 1) := by simp [D.ptSize]
      rw [e, hsz]
      omega
  set ut := utT p w.length c Fi L s h with hut
  set bt := btT p w.length c Fi L s h with hbt
  have hpi : (1 : ℝ) ≤ Real.pi ^ (s - 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  refine ⟨HT I Wp Wq, inferInstance, inferInstance, inferInstance, ut, bt, U.betaU, epsT s, -1, SS, 1,
    ((Real.pi ^ (s - 1))⁻¹) ^ 2, by positivity, ?_, Or.inr rfl, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : ((Real.pi ^ (s - 1))⁻¹) ^ 2 ≤ 1 := by
      have : (Real.pi ^ (s - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
      have h0 : 0 ≤ (Real.pi ^ (s - 1))⁻¹ := by positivity
      nlinarith
    linarith [Real.pi_gt_three]
  ·
    refine ⟨hs0, Formalism.FourierDecayAlt.P.scale_matching.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [epsT]
    · intro _ _ x hx
      exact hMU p nn F w c Fi L hV b s hb hs hbs' h hh x hx
    · intro _ _ x hx
      rw [hSU p nn F w c Fi L hV b s hb hs hbs' h hh x hx]
      have := hSS ⟨⟨x⁻¹, inv_ne_zero hx⟩, rfl⟩
      simp only at this
      rwa [hr2] at this
    · intro _ _
      exact hME p nn F w c Fi L hV b s hb hs hbs' h hh
    · intro _ _ K' hK' hK0
      exact hLO p nn F w c Fi L hV b s hb hs hbs' h hh K' hK' hK0
    · intro _ _ K' hK' hK0
      choose Ci hCi using fun i => hTC Wp Wq P p (Fi i) (hFi i) w.length b s hb hs hbs' h hh K' hK' hK0
      refine ⟨∑ i, √(c i) * ‖L i‖ * Ci i, fun x hx => Eventually.of_forall fun D hD => ?_⟩
      have hD0 : D ≠ 0 := fun h0 => hK0 (h0 ▸ hD)
      have heD : epsT s * D ≠ 0 := mul_ne_zero (by simp [epsT]) hD0
      have hroot : ∀ z ∈ G.rootSet s (epsT s * D), z ≠ 0 := by
        intro z hz h0
        unfold G.rootSet at hz
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hz
        rw [h0, zero_pow hs0] at hz
        exact heD hz.symm

      have hsum : ut x D - PBK.mainD s U.betaU (epsT s) bt x D =
          ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), coT s x j • vecT p w.length c Fi L (ptT s h x D j) := by
        rw [Finset.sum_insertNone, sub_eq_add_neg]
        refine congrArg₂ (· + ·) rfl ?_
        · unfold PBK.mainD
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun z hzm => ?_
          simp only [hbt, btT, if_neg (hroot z hzm), coT, ptT, smul_smul, neg_smul, neg_mul]
      rw [hsum]
      have hk : ∀ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), ∀ l ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          ⟪vecT p w.length c Fi L (ptT s h x D j), vecT p w.length c Fi L (ptT s h x D l)⟫_ℂ =
            ∑ i, (c i : ℂ) * ⟪(omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j)),
              (omT p w.length (ptT s h x D l) : ℂ) • L i (p.V (Fi i) (ptT s h x D l))⟫_ℂ :=
        fun j _ l _ => inner_vecT p w.length c hc Fi L _ _
      refine (norm_sum_le_of_gram' (vecT p w.length c Fi L) c hc
        (fun i Q => (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)) _ (ptT s h x D) hk (coT s x)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      have e : ∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
          coT s x j • ((omT p w.length (ptT s h x D j) : ℂ) • L i (p.V (Fi i) (ptT s h x D j))) =
          L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_smul]
      rw [e]
      have h3 := hCi i x hx D hD
      have hsq := Real.sqrt_nonneg (c i)
      calc √(c i) * ‖L i (∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j))‖
          ≤ √(c i) * (‖L i‖ * ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)),
            (coT s x j * (omT p w.length (ptT s h x D j) : ℂ)) • p.V (Fi i) (ptT s h x D j)‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hsq
        _ ≤ √(c i) * (‖L i‖ * (Ci i * ‖x‖⁻¹)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) hsq
        _ = √(c i) * ‖L i‖ * Ci i * ‖x‖⁻¹ := by ring
  ·
    intro σ z
    have hbU : U.betaU = 2 * Complex.I := by
      unfold U.betaU Formalism.QuantumDeterminants.cStd; ring
    unfold P5.fsv G.psi
    rw [hbU]
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  ·
    intro t t' ht ht'
    have hx : t⁻¹ ≠ 0 := inv_ne_zero ht
    have hx' : t'⁻¹ ≠ 0 := inv_ne_zero ht'
    have hg : PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹) =
        ∫ cc : ℂ, TBB.NP p nn F (P.r + 1) w ((h ++ [(s - 1, t')]) ++ [(1, cc)]) ((h ++ [(s - 1, t)]) ++ [(1, cc)]) := by
      unfold PBK.gramL PBK.Uc
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only [hut]
      rw [cvec_utT p w.length c Fi L s h _ hx, cvec_utT p w.length c Fi L s h _ hx', inv_inv, inv_inv,
        inner_vecT_np p nn F w c Fi L hV]
    have hn : TBB.NP p nn F (b + s - 2) w (h ++ [(s - 1, t)]) (h ++ [(s - 1, t')]) =
        conj (PBK.gramL volume (PBK.Uc s fun _ : Unit => ut) (PBK.Uc s fun _ : Unit => ut) ((), t⁻¹) ((), t'⁻¹)) := by
      rw [hg, hr2, hV.fibre _ _ (hloc t ht) (hloc t' ht'), ← integral_conj]
      refine integral_congr_ae (Eventually.of_forall fun cc => ?_)
      simp only
      rw [← inner_vecT_np p nn F w c Fi L hV, ← inner_vecT_np p nn F w c Fi L hV, inner_conj_symm]
    rw [hn, RCLike.norm_conj, one_mul]
  ·
    intro z hz
    have hQ : TBB.Ew p nn F (b + s - 1) w (h ++ [(s, z)]) = ‖vecT p w.length c Fi L (h ++ [(s, z)])‖ ^ 2 := by
      unfold TBB.Ew
      rw [hr1, ← inner_vecT_np p nn F w c Fi L hV, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hbz : PBK.bz s bt z = ((Real.pi ^ (s - 1) : ℝ) : ℂ) • vecT p w.length c Fi L (h ++ [(s, z)]) := by
      simp only [PBK.bz, hbt, btT, if_neg hz, smul_smul, ← Complex.ofReal_mul]
      congr 2
      have hpos : (0 : ℝ) < (s : ℝ) * ‖z‖ ^ (s - 1) := by
        have : (0 : ℝ) < ‖z‖ ^ (s - 1) := pow_pos (norm_pos_iff.mpr hz) _
        have hs' : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
        positivity
      field_simp
    rw [hQ, hbz, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ (by positivity), one_pow, one_mul]

end
end Formalism.FourierDecayAlt.P.CutBP.GT

namespace Formalism.FourierDecayAlt.P.CutBP

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.germ_data_top_levelCpt : GermDataTopAllCpt :=
  GT.germDataTopAll_of_partsCpt GT.top_level_gram GT.top_level_germ_leading GT.top_level_fibreCpt GT.top_level_Y_continuity
    GT.field_mem_unitary GT.field_supremum GT.field_measurability GT.field_locality

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.block_growth_bound_of_germ_dataCpt (hA : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hC : GermContAll) (hL : GermDataLowAllCpt) (hT : GermDataTopAllCpt) (hM : PropGMean) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_positive_germ p nn G Y K N (posAt_of_cptCpt hA p nn G Y N (fun y => (hnn y).le) hG)
    (germAtPD_of_parts p nn G Y K N (hC Wp Wq P p nn G Y K N Cb hCb hG hnn) (hL hA Wp Wq P p nn G Y K N Cb hCb hG hnn)
      (hT hA Wp Wq P p nn G Y K N Cb hCb hG hnn) hM)

end Formalism.FourierDecayAlt.P.CutBP

namespace Formalism.FourierDecayAlt.P.CutBP
open Formalism.FourierDecayAlt

theorem _root_.Formalism.FourierDecayAlt.P.CutBP.block_growth_bound_of_compact_coef_of_germ_dataCpt (hA : P5.ThmPActualCpt) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hL : GermDataLowAllCpt) (hT : GermDataTopAllCpt) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_germ_dataCpt hA p nn G Y K N Cb hCb hG hnn germ_continuity_all_levels hL hT germ_mean_property

end Formalism.FourierDecayAlt.P.CutBP

set_option maxHeartbeats 0 in
cpt_copy_thms
