import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SumSingleEmbeddingExtendLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlagSpanBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma neg_log_epStar (M f w k0 : ℝ) (hM : 0 < M) (hfw : 0 < f * w + 2) (hk0 : 0 < k0) (hk0' : k0 ≤ 2) :
    -Real.log (epStar M f w k0) ≤ max 0 (Real.log M + Real.log (f * w + 2) + Real.log 2) := by
  unfold epStar
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < M * (f * w + 2) * k0 * Real.log 2 := by positivity
  rcases le_total 1 (Real.pi / (M * (f * w + 2) * k0 * Real.log 2)) with hq | hq
  · rw [min_eq_left hq, Real.log_one]; simp
  · rw [min_eq_right hq, Real.log_div Real.pi_pos.ne' hden.ne', Real.log_mul (by positivity) hl2.ne',
      Real.log_mul (by positivity) hk0.ne', Real.log_mul hM.ne' hfw.ne']
    have h1 : Real.log k0 ≤ Real.log 2 := Real.log_le_log hk0 hk0'
    have h2 : Real.log (Real.log 2) ≤ 0 := Real.log_nonpos hl2.le (by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith)
    have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    have h4 := le_max_right 0 (Real.log M + Real.log (f * w + 2) + Real.log 2)
    linarith

theorem lam1Row (hMD : ModelDataXSt) : Lam1RowSt := by
  intro D T h hGam large₂ j hj w hrows hL hrn hlast σ hσ f hf k z0 hz0 hhalf hpos
  obtain ⟨e, M, wg, hM, hlM, hwg, hsp, htr, hfw, ⟨B, hlB, hB⟩, hk0⟩ := hMD D T h hGam large₂ j hj w hrows hL hrn σ hσ k

  have hcusp := ((mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  let S : Submodule ℂ (FDSec (T.U j σ).X) :=
    { carrier := {Q | ∀ k, Q k ∈ ((T.U j σ).X k).SS (laU (T.U j σ) (wtA w) w.n k)}
      add_mem' := by
        intro Q R hQ hR k
        refine ⟨BoundedSectionAlgebra.bdd_add _ (hQ k).1 (hR k).1, fun ξ hξ x hx => ?_⟩
        have e1 := BoundedSectionAlgebra.fj_add _ (hQ k).1 (hR k).1 hξ hx 0
        rw [(hQ k).2 ξ hξ x hx, (hR k).2 ξ hξ x hx, add_zero] at e1
        exact e1
      zero_mem' := fun k => ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
      smul_mem' := by
        intro c Q hQ k
        refine ⟨BoundedSectionAlgebra.bdd_smul _ c (hQ k).1, fun ξ hξ x hx => ?_⟩
        have e1 := BoundedSectionAlgebra.fj_smul _ (laU (T.U j σ) (wtA w) w.n k) (Q k) ξ x 0 c
        rw [(hQ k).2 ξ hξ x hx, mul_zero] at e1
        exact e1 }
  have hSS : rdU (T.U j σ) f k ∈ ((T.U j σ).X k).SS (laU (T.U j σ) (wtA w) w.n k) :=
    (Submodule.span_le.2 (fun Q hQ k => hQ k) : holSub _ _ ≤ S) hcusp k
  have hmax := maxBound_holds D.R.r e.toX (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) M wg hSS hM hsp
    hwg htr z0 hz0 hhalf hpos

  have hfw0 : 0 < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  set ep := epStar M (fdeg D.host.E) wg e.k0 with hepdef
  have hep : 0 < ep := by
    rw [hepdef]; unfold epStar
    exact lt_min one_pos (div_pos Real.pi_pos
      (mul_pos (mul_pos (mul_pos hM hfw0) e.minWeight_pos) (Real.log_pos (by norm_num))))
  have hmax' : ∀ v ∈ e.L', v ≠ 0 → ∃ τ : ((T.U j σ).X k).Ψ,
      ep ≤ ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := hmax
  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = e.k0 := fun τ => by
    unfold Data.c; rw [e.ξ0_abs τ]; ring

  have hr : 0 < D.R.r := (PfTies1.dimPos_fr D).2
  have hne : ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 := by
    have hL' : ∃ y ∈ e.L', y ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hx0 : (Pi.single (⟨0, hr⟩ : Fin D.R.r) (1 : D.host.E)) ∈ e.L' := by
        refine e.L'_dual _ (fun y hy => ?_)
        rw [hcon y hy]
        simp [herm]
        exact isIntegral_zero
      exact Pi.single_ne_zero_iff.2 one_ne_zero (hcon _ hx0)
    obtain ⟨y, hy, hy0⟩ := hL'
    exact ⟨_, e.NC_sub y hy, smul_ne_zero (Nat.cast_ne_zero.2 e.NC_pos.ne') hy0⟩
  obtain ⟨v0, hv0, hv00⟩ := hne
  have hBpos : 0 < B := by
    obtain ⟨a, ha0, -, hab⟩ := hB v0 hv0 hv00
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact lt_of_lt_of_le (norm_pos_iff.2 ((map_ne_zero τ).2 ha0)) (hab τ)
  set m := e.k0 * ep / B ^ 2 with hmdef
  have hm : 0 < m := div_pos (mul_pos e.minWeight_pos hep) (pow_pos hBpos 2)
  have hlow : ∀ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 → m ≤ ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := by
    intro v hv hv0
    obtain ⟨a, ha0, hav, hab⟩ := hB v hv hv0
    obtain ⟨τ0, hτ0'⟩ := hmax' _ hav (smul_ne_zero ha0 hv0)
    have hemb : Data.emb τ0.1 (a • v) = (τ0.1 a) • Data.emb τ0.1 v := by
      funext i; simp [Data.emb]
    rw [hemb, Data.maj_smul ((T.U j σ).X k) (Data.Hf_self ((T.U j σ).X k) hz0 τ0)] at hτ0'
    have hmaj0 := FlagSpanBounds.maj_nonneg ((T.U j σ).X k) hz0 τ0 (Data.emb τ0.1 v)
    have hns : Complex.normSq (τ0.1 a) ≤ B ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hab τ0.1) 2
    have hterm : ∀ τ, 0 ≤ ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) := fun τ =>
      mul_nonneg (by rw [hc]; exact e.minWeight_pos.le) (FlagSpanBounds.maj_nonneg ((T.U j σ).X k) hz0 τ _)
    have h1 : ep / B ^ 2 ≤ ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := by
      rw [div_le_iff₀ (pow_pos hBpos 2)]; nlinarith
    calc m = e.k0 * (ep / B ^ 2) := by rw [hmdef]; ring
      _ ≤ e.k0 * ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := mul_le_mul_of_nonneg_left h1 e.minWeight_pos.le
      _ = ((T.U j σ).X k).c τ0 * ((T.U j σ).X k).maj z0 τ0 (Data.emb τ0.1 v) := by rw [hc]
      _ ≤ ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (Data.emb τ.1 v) :=
        Finset.single_le_sum (fun τ _ => hterm τ) (Finset.mem_univ τ0)
  have hle : m ≤ ((T.U j σ).X k).firstMinimumSq z0 :=
    le_csInf ⟨_, v0, hv0, hv00, rfl⟩ (fun t ⟨v, hv, hv0', ht⟩ => ht ▸ hlow v hv hv0')
  refine ⟨lt_of_lt_of_le hm hle, ?_⟩
  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ Real.log (1 / m) :=
    Real.log_le_log (one_div_pos.2 (lt_of_lt_of_le hm hle)) (one_div_le_one_div_of_le hm hle)
  have h2 : Real.log (1 / m) = -Real.log e.k0 - Real.log ep + 2 * Real.log B := by
    rw [hmdef, one_div, Real.log_inv, Real.log_div (mul_pos e.minWeight_pos hep).ne' (pow_pos hBpos 2).ne',
      Real.log_mul e.minWeight_pos.ne' hep.ne', Real.log_pow]
    push_cast; ring
  have h3 := neg_log_epStar M (fdeg D.host.E) wg e.k0 hM hfw0 e.minWeight_pos e.k0_le
  have h4 : -Real.log e.k0 ≤ 3 * large₂.sc.L := by rw [one_div, Real.log_inv] at hk0; linarith
  have h5 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h6 : max 0 (Real.log M + Real.log ((fdeg D.host.E : ℝ) * wg + 2) + Real.log 2) ≤ 32 * large₂.sc.L + 1 :=
    max_le (by linarith) (by linarith)
  rw [← hepdef] at h3
  linarith

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row
