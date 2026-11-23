import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumQuotientTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasSumDoublingInert
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LvTwDivDvInertEqStdL
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LocZetaInertAd

theorem domain_of_bound {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (α : Fin (n / 2) → ℂˣ) {ε : ℂ} (hε : ‖ε‖ = 1) {s : ℂ}
    (hs : (n : ℝ) < s.re) (hα : ∀ i, ‖((α i : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) ∧
      ‖(((α i)⁻¹ : ℂˣ) : ℂ)‖ ≤ ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s) α := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hy : ‖GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q ε s‖ = (q : ℝ) ^ (-(2 * s.re + 1)) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    congr 1
    simp
  have hQ : ((q ^ 2 : ℕ) : ℝ) ^ ((n : ℝ) / 2) = (q : ℝ) ^ (n : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have key : (q : ℝ) ^ (-(2 * s.re + 1)) * (q : ℝ) ^ (n : ℝ) < 1 := by
    rw [← Real.rpow_add hq0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-(2 * s.re + 1)) := (Real.rpow_pos_of_pos hq0 _).le
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · rw [hy]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  · rw [hy]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((hα i).1.trans hQ.le) hpos) key
  · rw [hy]
    have := (hα i).2
    rw [Units.val_inv_eq_inv_val, norm_inv] at this
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (this.trans hQ.le) hpos) key

end GlobalTheory.LocZetaInertAd

namespace GlobalTheory.LocZetaInertAd

set_option maxHeartbeats 400000 in
theorem localZetaOn_inert : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D (fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → LocalZetaOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hU D hPB A L hL χ b hχ hRes v hv hunr μ hμ hμK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨-, V, _, _, ρ, x, ℓ, hpar, hℓ, hcx⟩ := hc'
  have hfix := (hpar w h).mem_fixed
  rcases hpar w h with ⟨hsplit, -⟩ | ⟨hw, c', ϖ0, e, α, hUI, he, hsat, hBw⟩
  · exact absurd hsplit hv
  have hϖ0 : ϖ0 ≠ 0 := by
    intro h0
    have := hUI.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let ϖ : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ0 hϖ0
  obtain ⟨hUnr, hχϖ, hχϖb, Φ, hΦ, hφΦ⟩ := GlobalTheory.KerInert.sphSec_inert D A L hL χ b hRes v w h hw (hunr w h) s φ hφ c' ϖ e hUI he
  let ρ' : Representation ℂ (Formalism.UG.GU c' A.rank) V := ρ.comp e.symm.toMonoidHom
  have hℓ' : ∀ k ∈ Formalism.UG.KU c' A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := (he.2.2 _).2 (by simpa using hk)
    have := hℓ _ hk' (e.symm g)
    simpa [ρ'] using this
  have hdom : ℓ x ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY (Formalism.UG.qV D.host.F v) (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) s) α := by
    intro hx0
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact hx0
    obtain ⟨-, hbd⟩ := hPB A L hL v hv par c hc hc1 w h
    have hN : Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v ^ 2 := GlobalTheory.LFun.InertChart.absNorm_eq h2 hw
    have hq : 2 ≤ Formalism.UG.qV D.host.F v := hUI.2.2.2.2.2.1
    refine GlobalTheory.LocZetaInertAd.domain_of_bound hq α (GlobalTheory.LFun.norm_locChar _ _ _) (by exact_mod_cast hs) fun i => ?_
    have h1 := hbd (α i) (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    have h3 := hbd (α i)⁻¹ (by rw [hBw]; simp [GlobalTheory.LGrp.bcParam])
    rw [hN] at h1 h3
    exact ⟨h1, h3⟩
  obtain ⟨hΦK, hsum⟩ := GlobalTheory.DoublingSumU.hasSum_doubling_inert hU (w.adicCompletion D.host.E) ϖ c' (Formalism.UG.qV D.host.F v) A.rank hUI
    (GlobalTheory.LFun.locChar χ⁻¹ w) hUnr b hχϖb s Φ hΦ V ρ' x α hsat ℓ hℓ' hdom
  have hsum' : HasSum (fun a : Gv A v ⧸ stabLoc D.sp.cm.sig A.gram L v =>
      φ (ioAt A v a.out) * c a.out)
      (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.stdL (Formalism.UG.qV D.host.F v) A.rank α (GlobalTheory.LFun.locChar χ⁻¹ w ϖ) (s + 1 / 2) /
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.dFac (Formalism.UG.qV D.host.F v) A.rank b s * ℓ x) := by
    refine GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e _ _ he.2.2 (fun g => φ (ioAt A v g) * c g) ?_ _ ?_
    · intro g k hk
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]
    · have hfun : ∀ a : Formalism.UG.GU c' A.rank ⧸ Formalism.UG.KU c' A.rank, φ (ioAt A v (e.symm a.out)) * c (e.symm a.out) =
          Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c' A.rank a.out) * ℓ (ρ' a.out x) := fun a => by
        rw [hφΦ, hcx, MulEquiv.apply_symm_apply]; rfl
      simp only [hfun]
      exact hsum
  haveI := hL.1
  obtain ⟨hint, hval⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v) (isOpen_stabLoc _ _ _ v) hμK
    (fun g => φ (ioAt A v g) * c g) _ (fun g k hk => by
      show φ (ioAt A v (g * k)) * c (g * k) = φ (ioAt A v g) * c g
      rw [hφΦ, hφΦ, map_mul, hΦK _ _ ((he.2.2 k).1 hk), hcx, hcx, map_mul, Module.End.mul_apply,
        GlobalTheory.LGrp.mem_fixed.1 hfix k hk]) hsum'
  refine ⟨hint, ?_⟩
  rw [hval, GlobalTheory.LFun.LvTw_div_dv_inert_eq_stdL _ _ par (GlobalTheory.LFun.val χ) v w A.rank b α s h2 hw (GlobalTheory.LFun.isUnram_of_isInertAt hw) hBw, ← hχϖ,
    hcx 1, map_one, Module.End.one_apply]

end GlobalTheory.LocZetaInertAd
