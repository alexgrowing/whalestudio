import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH_SFG_PtGV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFGCkExt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialBesselSmoothCompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sliceFamGood_of (hGf : GfStep) (hRP : RadProper) (hPS : ParamSmooth) (hPt : PtSmooth) (hGV : PtGV)
    (hE : CkExt) : CutSH.SliceFamGood := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j hj _ _ F hF
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  obtain ⟨⟨hcc, ε, hε, hFG⟩, hcs⟩ := hF
  have hFs : B.CkOn (⊤ : ℕ∞) (B.GV P.k (P.r - j)) F :=
    Formalism.FourierDecayAlt.P.PBE.ckOn_top_of_nat fun m => (hcc 0 m).choose_spec.1
  obtain ⟨Ft, hFt, -, hFtF⟩ := hE P.k (P.r - j) _ F hFs hcs
  obtain ⟨R, hR⟩ := (hcs.isCompact.image_of_continuousOn
    (Formalism.FourierDecayAlt.P.B6.gN_continuous (k := P.k) (r := P.r - j)).continuousOn).bddAbove
  have hRF : ∀ g, F g ≠ 0 → B.gN g ≤ R := fun g hne => hR ⟨g, subset_tsupport _ hne, rfl⟩
  have hsl : ∀ (t : ℂ) (γ : B.Mat P.k (P.r - (j + 1))), γ ∈ B.GV P.k (P.r - (j + 1)) → sliceFam T j hj F t γ =
      ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) * star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
          F (pt e t γ xx) ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) := by
    intro t γ hγ
    unfold sliceFam
    rw [Set.indicator_of_mem hγ]
    rfl
  refine ⟨?_, ?_⟩
  ·
    intro t₀ ht₀ γ₀ _
    have ht₀p : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀
    set δ : ℝ := ‖t₀‖ / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    obtain ⟨Kx, C, hKx, -, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e δ R hδ0
    obtain ⟨R1, hR1⟩ :=
      hKx.isBounded.subset_closedBall (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)))
    have : HasContDiffBump (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := inferInstance
    set χ : ContDiffBump (0 : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) :=
      ⟨max R1 0 + 1, max R1 0 + 2, by positivity, by linarith⟩ with hχ
    set s : Set (ℂ × B.Mat P.k (P.r - (j + 1))) := {p | δ < ‖p.1‖} with hs
    have hso : IsOpen s := isOpen_lt continuous_const (continuous_norm.comp continuous_fst)
    have hs0 : ∀ p ∈ s, p.1 ≠ 0 := fun p hp => norm_pos_iff.1 (hδ0.trans hp)
    set hI : ℂ × B.Mat P.k (P.r - (j + 1)) → U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)) →
        (Wq →L[ℂ] Wp) :=
      fun p xx => χ xx • ((psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
        star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) • Ft (pt e p.1 p.2 xx)) with hIdef
    refine ⟨s, fun p => ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
      ∫ xx, hI p xx ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))), hso, ?_, ?_, ?_⟩
    · show δ < ‖t₀‖
      rw [hδ]; linarith
    ·
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have : BorelSpace (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) := Prod.borelSpace
      have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := P.k) 1 (P.r - (j + 1))
      have := Formalism.FourierDecayAlt.P.PartialBesselLeftWordLemmas.fmc_RC P.k 1 (P.r - (j + 1))
      have hsc : ContDiffOn ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) =>
          ((‖p.1‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ)) s := by
        intro p hp
        have hn : ContDiffAt ℝ ∞ (fun p : ℂ × B.Mat P.k (P.r - (j + 1)) => ‖p.1‖) p :=
          (contDiffAt_norm ℝ (hs0 p hp)).comp p contDiffAt_fst
        exact (Complex.ofRealCLM.contDiff.contDiffAt.comp p (hn.pow _)).contDiffWithinAt
      have hps := (hPt P.k (P.r - (j + 1)) (P.r - j) e).2
      have hpt := (hPt P.k (P.r - (j + 1)) (P.r - j) e).1
      have hjoint : ContDiffOn ℝ ∞
          (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) × (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            hI q.1 q.2) (s ×ˢ Set.univ) := by
        have h1 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => χ q.2) :=
          χ.contDiff.comp contDiff_snd
        have h2 : ContDiff ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) =>
            psi P.k (P.r - j) (T.bs j).z cStd (rn1 e q.2.1) *
              star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e q.2.2))) := by
          refine ((hps (T.bs j).z).comp (contDiff_fst.comp contDiff_snd)).mul ?_
          exact Complex.conjCLE.contDiff.comp ((hps (T.bs j).z').comp (contDiff_snd.comp contDiff_snd))
        have h3 : ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat P.k (P.r - (j + 1))) ×
            (U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1))) => Ft (pt e q.1.1 q.1.2 q.2))
            (s ×ˢ Set.univ) :=
          hFt.comp_contDiffOn (hpt.mono (Set.prod_mono (fun p hp => hs0 p hp) le_rfl))
        exact h1.contDiffOn.smul (h2.contDiffOn.smul h3)
      have hvan : ∀ p ∈ s, ∀ xx, xx ∉ tsupport χ → hI p xx = 0 := by
        intro p _ xx hxx
        simp only [hIdef, image_eq_zero_of_notMem_tsupport hxx, zero_smul]
      have hint := hPS _ _ _ ((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))) hI s
        (tsupport χ) hso χ.hasCompactSupport hvan hjoint
      exact hsc.smul hint
    ·
      rintro ⟨t, γ⟩ hp hγ
      have ht : t ≠ 0 := hs0 _ hp
      have hδt : δ ≤ ‖t‖ := le_of_lt hp
      show sliceFam T j hj F t γ = _
      rw [hsl t γ hγ]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have hFt' : Ft (pt e t γ xx) = F (pt e t γ xx) := hFtF _ hpG
      show _ = hI (t, γ) xx
      simp only [hIdef]
      rw [hFt']
      by_cases hF0 : F (pt e t γ xx) = 0
      · simp only [hF0, smul_zero]
      · have hxK : xx ∈ Kx := (hKC t γ xx hδt (hRF _ hF0)).1
        have h1 : χ xx = 1 := by
          apply χ.one_of_mem_closedBall
          have := hR1 hxK
          rw [Metric.mem_closedBall] at this ⊢
          show dist xx 0 ≤ max R1 0 + 1
          linarith [le_max_left R1 0]
        rw [h1, one_smul]
  ·
    intro K hK hK0
    by_cases hne : K.Nonempty
    · obtain ⟨t1, ht1K, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
      have hδ0 : 0 < ‖t1‖ := norm_pos_iff.2 (hK0 t1 ht1K)
      obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
      have hM' : ∀ t ∈ K, ‖t‖ ≤ M := fun t ht => by simpa using hM t ht
      have hMp : 0 < M := hδ0.trans_le (hM' t1 ht1K)
      obtain ⟨Kx, C, -, hC, hKC⟩ := hRP P.k (P.r - (j + 1)) (P.r - j) e ‖t1‖ R hδ0
      refine ⟨C, hC, ε / M ^ 2, by positivity, ?_⟩
      intro t htK γ hne'
      have ht : t ≠ 0 := hK0 t htK
      have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := by
        by_contra hγ
        apply hne'
        unfold sliceFam
        rw [Set.indicator_of_notMem hγ]
      rw [hsl t γ hγ] at hne'
      obtain ⟨xx, hxx⟩ : ∃ xx, F (pt e t γ xx) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne'
        simp only [hall, smul_zero, integral_zero]
      have hδt : ‖t1‖ ≤ ‖t‖ := hmin htK
      refine ⟨(hKC t γ xx hδt (hRF _ hxx)).2, fun _ => ?_⟩
      have hpG := hGV P.k (P.r - (j + 1)) (P.r - j) e t ht γ hγ xx
      have h1 : ε ≤ Gf P.k (P.r - j) (T.bs j).z (T.bs j).z' (pt e t γ xx) := hFG _ hpG hxx
      have hz : (T.bs j).z = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z)) := by
        rw [levTower_bs_z_eq_castV_liftVec T j hj, asm_castV_castV]
      have hz' : (T.bs j).z' = D.castV e (D.castV (Nat.add_comm 1 (P.r - (j + 1)))
          (liftVec P.k 1 (P.r - (j + 1)) (T.bs (j + 1)).z')) := by
        rw [levTower_bs_z'_eq_castV_liftVec T j hj, asm_castV_castV]
      rw [hz, hz', hGf P.k (P.r - (j + 1)) (P.r - j) e _ _ (T.bs (j + 1)).z_mem (T.bs (j + 1)).z'_mem t ht γ xx]
        at h1
      have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
      have htM : ‖t‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM' t htK) 2
      have hG0 : 0 < Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ := by
        by_contra hle
        push Not at hle
        have : ‖t‖ ^ 2 * Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · exact ⟨∅, isCompact_empty, 1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩

end Formalism.FourierDecayAlt.P.CutSH.SFG

namespace Formalism.FourierDecayAlt.P.CutSH

theorem cutSH_sliceFamGood_of (hGf : SFG.GfStep) (hRP : SFG.RadProper) (hPS : SFG.ParamSmooth)
    (hPt : SFG.PtSmooth) : SliceFamGood :=
  SFG.sliceFamGood_of hGf hRP hPS hPt SFG.point_mem_unitary_group SFG.ckExt_proof

end Formalism.FourierDecayAlt.P.CutSH
