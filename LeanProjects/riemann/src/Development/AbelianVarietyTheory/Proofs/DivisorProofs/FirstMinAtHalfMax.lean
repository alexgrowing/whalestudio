import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualDataTransvectionPrincipalLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankRieszBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBounds

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped nonZeroDivisors

namespace GlobalTheory.RawThetaSup

set_option maxHeartbeats 800000 in

theorem exists_small_inv (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ξ : K) (x : ℝ) (hx : 0 < x)
    (hξ : ∀ τ : K →+* ℂ, ‖τ ξ‖ = x) (A B : FractionalIdeal (𝓞 K)⁰ K)
    (h : FractionalIdeal.spanSingleton (𝓞 K)⁰ ξ * A * B * (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) = 1)
    (hAB : FractionalIdeal.absNorm B ≤ FractionalIdeal.absNorm A) :
    ∃ b : K, b ≠ 0 ∧ (∀ a ∈ A, IsIntegral ℤ (b * a)) ∧ ∀ τ : K →+* ℂ, ‖τ b‖ ^ 2 ≤ x * rdE K ^ 2 := by
  have hA : A ≠ 0 := by rintro rfl; simp at h
  obtain ⟨c, hc⟩ : ∃ c, c = InfinitePlace.nrComplexPlaces K := ⟨_, rfl⟩
  have hn : Module.finrank ℚ K = 2 * c := hc ▸ IsTotallyComplex.finrank K
  have hc0 : c ≠ 0 := by have := Module.finrank_pos (R := ℚ) (M := K); omega
  have hcard : Fintype.card (InfinitePlace K) = c := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add, hc]
  have hd : 0 < |(discr K : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hNξ : ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) = x ^ (2 * c) := by
    rw [← InfinitePlace.prod_eq_abs_norm, ← hn, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← hξ w.embedding, InfinitePlace.norm_embedding_eq]
  have hN := congrArg FractionalIdeal.absNorm h
  rw [map_mul, map_mul, map_mul, map_one, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm,
    NumberField.absNorm_differentIdeal K (𝓞 K)] at hN
  have hN' : x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm B : ℝ) * |(discr K : ℝ)| = 1 := by
    rw [← hNξ]
    have := congrArg (Rat.cast : ℚ → ℝ) hN
    simpa [Nat.cast_natAbs] using this
  have hB0 : (0 : ℝ) ≤ (FractionalIdeal.absNorm B : ℝ) := by exact_mod_cast FractionalIdeal.absNorm_nonneg B
  have hAB' : (FractionalIdeal.absNorm B : ℝ) ≤ (FractionalIdeal.absNorm A : ℝ) := by exact_mod_cast hAB
  have hA0 : (0 : ℝ) < (FractionalIdeal.absNorm A : ℝ) := by
    rcases (hB0.trans hAB').eq_or_lt with e | e
    · rw [← e] at hN'; simp at hN'
    · exact e
  have hrd : rdE K ^ (2 * c) = |(discr K : ℝ)| := by
    unfold rdE dE
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le, hn, one_div_mul_cancel (by exact_mod_cast (by omega : 2 * c ≠ 0)),
      Real.rpow_one]
  have hrd0 : 0 < rdE K := Real.rpow_pos_of_pos hd _
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt |(discr K : ℝ)| := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hd
  have hss : s * s = |(discr K : ℝ)| := hs ▸ Real.mul_self_sqrt hd.le
  have hpos : 0 < x * rdE K ^ 2 := mul_pos hx (pow_pos hrd0 2)
  have hu : (FractionalIdeal.absNorm A : ℝ)⁻¹ ≤ x ^ c * s := by
    rw [inv_le_iff_one_le_mul₀ hA0]
    refine (one_le_sq_iff₀ (by positivity)).1 ?_
    calc (1 : ℝ) = x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm B : ℝ) * |(discr K : ℝ)| :=
          hN'.symm
      _ ≤ x ^ (2 * c) * (FractionalIdeal.absNorm A : ℝ) * (FractionalIdeal.absNorm A : ℝ) * |(discr K : ℝ)| := by gcongr
      _ = _ := by rw [← hss]; ring
  obtain ⟨b, hb, hb0, hbw⟩ := Formalism.ExtensionFiltration.mk_lt K (Units.mk0 A⁻¹ (inv_ne_zero hA)) (fun _ => Real.sqrt (x * rdE K ^ 2))
    (fun _ => Real.sqrt_pos.2 hpos) (by
      rw [Real.sq_sqrt hpos.le, Finset.prod_const, Finset.card_univ, hcard, mul_pow, ← pow_mul, hrd, ← hc, ← hs,
        Units.val_mk0, map_inv₀, Rat.cast_inv]
      calc (FractionalIdeal.absNorm A : ℝ)⁻¹ * 2 ^ c * s ≤ x ^ c * s * 2 ^ c * s := by gcongr
        _ = 2 ^ c * (x ^ c * |(discr K : ℝ)|) := by rw [← hss]; ring
        _ < _ := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ (by linarith [Real.pi_gt_three]) (by norm_num) hc0)
            (by positivity))
  refine ⟨b, hb0, fun a ha => ?_, fun τ => ?_⟩
  · have hm : b * a ∈ A⁻¹ * A := FractionalIdeal.mul_mem_mul hb ha
    rw [inv_mul_cancel₀ hA, FractionalIdeal.mem_one_iff] at hm
    obtain ⟨z, hz⟩ := hm
    rw [← hz]
    exact z.isIntegral_coe
  · have h1 := (hbw (InfinitePlace.mk τ)).le
    rw [InfinitePlace.apply] at h1
    exact (Real.le_sqrt (norm_nonneg _) hpos.le).1 h1

theorem exists_small_inv_AA (D : D7) : ∃ b : D.host.E, b ≠ 0 ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ (b * a)) ∧
    ∀ τ : D.host.E →+* ℂ, ‖τ b‖ ^ 2 ≤ xiR D * rdE D.host.E ^ 2 := by
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar *
      (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 1 :=
    Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hx := GlobalTheory.SupDict.xiR_pos D
  have hξ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D
  rcases le_total (FractionalIdeal.absNorm D.host.AAbar) (FractionalIdeal.absNorm D.host.AA) with h | h
  · exact exists_small_inv _ _ _ hx hξ _ _ h1 h
  · obtain ⟨b, hb0, hb, hτ⟩ := exists_small_inv _ _ _ hx hξ D.host.AAbar D.host.AA
      (by rw [← h1]; ring) h
    refine ⟨D.host.conj b, (map_ne_zero _).2 hb0, fun a ha => ?_, fun τ => ?_⟩
    · have := (hb _ (conj_mem_AAbar D ha)).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom
      simpa [conj_conj] using this
    · exact hτ (τ.comp (D.host.conj : D.host.E →+* D.host.E))

theorem epsLev_pos (E : Type) [Field E] [NumberField E] {d M : ℕ} (hd : 0 < d) (hM : 0 < M) {w : ℝ} (hw : 0 < w) :
    0 < epsLev E d M w := by
  unfold epsLev epStar
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact lt_min one_pos (div_pos Real.pi_pos (by positivity))

section Level

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem firstMin_at_halfMax (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp)
    (la : Wt ((U σ).X k).Ψ D.R.r) {w : ℝ} (hw0 : 0 < w) (hw : (∑ τ, ((U σ).X k).spread la τ) ≤ w)
    (hχ : ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ la γ = 1) {P : Frame ((U σ).X k).Ψ D.R.r → ℂ}
    (hP : P ∈ ((U σ).X k).SS la) {z0 : Frame ((U σ).X k).Ψ D.R.r} (hz0 : z0 ∈ ((U σ).X k).dom)
    (hhalf : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm la P x ≤ 2 * ((U σ).X k).pnorm la P z0)
    (hpos : 0 < ((U σ).X k).pnorm la P z0) :
    2 * epsLev D.host.E D.host.d l.M w / rdE D.host.E ^ 2 ≤ ((U σ).X k).firstMinimumSq z0 := by
  have habs := hLw.xiAbs σ hσ k
  obtain ⟨Xx, hX, -, hΛ, -, M', hM', hk, hT⟩ := exists_dataX_transv D j H Dw l Xo c U dict hLw σ hσ k
  generalize (U σ).X k = X at *
  subst hX
  have hmax := maxBound_holds D.R.r Xx la P M' w hP hM' hw hw0
    (fun v hv hiso b hb hbi => by
      obtain ⟨γ, hγ, he⟩ := hT v hv hiso b hb hbi
      exact ⟨γ, hγ, hχ γ hγ, he⟩) z0 hz0 hhalf hpos
  rw [GlobalTheory.SupModel.epStar_eq_epsLev D.host.d l.M w M' Xx.k0 hk] at hmax
  generalize epsLev D.host.E D.host.d l.M w = ep at hmax ⊢
  obtain ⟨b, hb0, hb, hbτ⟩ := exists_small_inv_AA D
  have hx := GlobalTheory.SupDict.xiR_pos D
  have hrd : 0 < rdE D.host.E := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (GlobalTheory.SupDict.one_le_dE _)) _
  have hc : ∀ τ : Xx.Ψ, Xx.toData.c τ = 2 * xiR D := fun τ => by unfold Data.c; rw [habs]
  have hsub : ∀ v ∈ Xx.Λ, b • v ∈ Xx.L' := by
    intro v hv
    rw [hΛ] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hx
      rw [smul_smul]
      exact Xx.L'.smul_mem (⟨b * a, hb a ha⟩ : 𝓞 D.host.E) hu
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Xx.L'.smul_mem c hx
  have hlow : ∀ v ∈ Xx.Λ, v ≠ 0 →
      2 * ep / rdE D.host.E ^ 2 ≤ ∑ τ, Xx.toData.c τ * Xx.toData.maj z0 τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨τ0, hτ0⟩ := hmax _ (hsub v hv) (smul_ne_zero hb0 hv0)
    have hemb : Data.emb τ0.1 (b • v) = τ0.1 b • Data.emb τ0.1 v := by
      funext a; simp [Data.emb]
    rw [hemb, FinrankRieszBounds.maj_csmul hz0] at hτ0
    have hm0 := fun τ => MajorantConjugateTransfer.maj_nonneg Xx.toData hz0 τ (Data.emb τ.1 v)
    have hterm : ∀ τ, 0 ≤ Xx.toData.c τ * Xx.toData.maj z0 τ (Data.emb τ.1 v) := fun τ =>
      mul_nonneg (by rw [hc]; positivity) (hm0 τ)
    refine le_trans ?_ (Finset.single_le_sum (fun τ _ => hterm τ) (Finset.mem_univ τ0))
    rw [hc, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right (hbτ τ0.1) (hm0 τ0)
    nlinarith
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hne : ∃ v ∈ Xx.Λ, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h1 : Submodule.span D.host.E (Xx.Λ : Set (Fin D.R.r → D.host.E)) = ⊥ := Submodule.span_eq_bot.2 hcon
    rw [Xx.Λ_span] at h1
    haveI : Nonempty (Fin D.R.r) := ⟨⟨0, hr⟩⟩
    exact top_ne_bot h1
  obtain ⟨v0, hv0, hv00⟩ := hne
  exact le_csInf ⟨_, v0, hv0, hv00, rfl⟩ (fun t ⟨v, hv, hv0', ht⟩ => ht ▸ hlow v hv hv0')

theorem half_sup_at_ortho (hLw : Laws D j Xo c U dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) {w : ℝ} (hw0 : 0 < w) (hw : ∀ k, (∑ τ, ((U σ).X k).spread (la k) τ) ≤ w)
    (hχ : ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (la k) γ = 1) {P : FDSec (U σ).X} (hP : P ∈ holSub (U σ).X la)
    (hpos : 0 < supN (U σ).X la P) :
    ∃ (k : (U σ).Comp) (xf : ((U σ).X k).dom), ((U σ).X k).IsOrtho xf.1 ∧ supN (U σ).X la P ≤ 2 * ‖P k xf.1‖ ∧
      2 * epsLev D.host.E D.host.d l.M w / rdE D.host.E ^ 2 ≤ ((U σ).X k).firstMinimumSq xf.1 := by
  have hSS := abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ).X la hP
  have hE : supE (U σ).X la P ≠ ⊤ := supE_ne_top _ la hP
  have hE0 : supE (U σ).X la P ≠ 0 := by
    intro h0; rw [supN, h0] at hpos; simp at hpos
  have hhalf' := ENNReal.half_lt_self hE0 hE
  unfold supE at hhalf'
  obtain ⟨p, hp⟩ := lt_iSup_iff.1 hhalf'
  have hp' : supN (U σ).X la P / 2 < ((U σ).X p.1).pnorm (la p.1) (P p.1) p.2 := by
    have := ENNReal.toReal_lt_of_lt_ofReal hp
    rw [ENNReal.toReal_div] at this
    simpa [supN, supE] using this
  have hle : ∀ q : Formalism.L2.Pj.FPt (U σ).X, ((U σ).X q.1).pnorm (la q.1) (P q.1) q.2 ≤ supN (U σ).X la P := by
    intro q
    have h1 : ENNReal.ofReal (((U σ).X q.1).pnorm (la q.1) (P q.1) q.2) ≤ supE (U σ).X la P :=
      le_iSup (fun q : Formalism.L2.Pj.FPt (U σ).X => ENNReal.ofReal (((U σ).X q.1).pnorm (la q.1) (P q.1) q.2)) q
    exact (ENNReal.ofReal_le_iff_le_toReal hE).1 h1
  obtain ⟨k, x, hx⟩ := p
  have hPS := (hSS k).1.1.2.1
  have hb := FrameDegreeData.bOf_mem ((U σ).X k) hx
  have hx' := OrthogonalFrameDomain.rmul_mem_dom ((U σ).X k) hx hb
  have hort := FrameDegreeData.ortho_bOf ((U σ).X k) hx
  have hunit := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((U σ).X k) hort
  have hpn := FrameDegreeData.pnorm_rmul ((U σ).X k) (la k) (P k) hPS x hx _ hb
  have hla := ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel ((U σ).X k) hx hb
  have h2 : supN (U σ).X la P ≤ 2 * ((U σ).X k).pnorm (la k) (P k) x := by linarith [hp']
  have hposx : 0 < ((U σ).X k).pnorm (la k) (P k) x := by linarith
  have hl := firstMin_at_halfMax hLw hσ k (la k) hw0 (hw k) (hχ k) (hSS k) hx
    (fun y hy => le_trans (hle ⟨k, y, hy⟩) h2) hposx
  refine ⟨k, ⟨_, hx'⟩, hort, ?_, by rw [hla]; exact hl⟩
  rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((U σ).X k) (la k) (P k) hunit, hpn]
  exact h2

end Level

end GlobalTheory.RawThetaSup
