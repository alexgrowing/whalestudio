import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOrEqNegOfPurelyImaginaryOfNormEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvMem
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHostStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModelWeightSizeSpreadBoundStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.CuspDataBounds

theorem exists_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (X : Data E r)
    (hX : Xx.toData = X) (S : Set E)
    (hΛ : Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ S, ∃ u ∈ Xx.L', v = a • u})
    (NA NC : ℕ) (hA : 0 < NA) (hC : 0 < NC) (hAi : ∀ a ∈ S, IsIntegral ℤ ((NA : E) * a)) (hCS : (NC : E) ∈ S) :
    ∃ e : XExt X, e.NA = NA ∧ e.NC = NC ∧ e.g = Xx.g ∧ e.k0 = Xx.k0 := by
  subst hX
  refine ⟨⟨Xx.k0, Xx.minWeight_pos, Xx.k0_le, Xx.ξ0_abs, Xx.EF_int, Xx.EF_perf, Xx.L', Xx.L'_fg, Xx.L'_int,
      Xx.L'_dual, NA, NC, hA, hC, ?_, ?_, Xx.g, Xx.g_pos, Xx.cong⟩, rfl, rfl, rfl, rfl⟩
  ·
    intro x hx
    rw [hΛ] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hy
      rw [smul_smul]
      have h1 : ((NA : E) * a) • u = (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) • u := by
        rw [← algebraMap_smul E (⟨(NA : E) * a, hAi a ha⟩ : 𝓞 E) u]
        rfl
      rw [h1]
      exact Xx.L'.smul_mem _ hu
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact Xx.L'.add_mem hy hz
    | smul c y _ hy =>
      rw [smul_comm]
      exact Xx.L'.smul_mem c hy
  ·
    intro x hx
    rw [hΛ]
    exact Submodule.subset_span ⟨(NC : E), hCS, x, hx, rfl⟩

theorem weight_bounds (L f r n d : ℝ) (hL : 2 ≤ L) (hf : 1 ≤ f) (hfr : f ≤ r) (hrn : r ≤ n) (hd : 0 ≤ d)
    (hn : Real.log n ≤ L) (hD : Real.log (1 + d) ≤ 2 * L) :
    Real.log (d + f * n + 1) ≤ 3 * L ∧ Real.log (f * (d + f * n + 1) + 2) ≤ 5 * L ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ d + f * r * n / 2 → Real.log (1 + s) ≤ 3 * L := by
  have hx3 : 3 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e2 : Real.exp (2 * L) = Real.exp L ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  have e3 : Real.exp (3 * L) = Real.exp L ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have e5 : Real.exp (5 * L) = Real.exp L ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  set x := Real.exp L with hx
  have hn0 : 0 < n := by linarith
  have hnx : n ≤ x := (Real.log_le_iff_le_exp hn0).1 hn
  have hdx : 1 + d ≤ x ^ 2 := by rw [← e2]; exact (Real.log_le_iff_le_exp (by linarith)).1 hD
  have hfx : f ≤ x := by linarith
  have hrx : r ≤ x := by linarith
  have hfn : f * n ≤ x ^ 2 := by nlinarith
  have hfn0 : 0 ≤ f * n := by nlinarith
  have hx2 : 9 ≤ x ^ 2 := by nlinarith
  have hx23 : 3 * x ^ 2 ≤ x ^ 3 := by nlinarith
  have hx35 : 9 * x ^ 3 ≤ x ^ 5 := by nlinarith
  have hA : d + f * n + 1 ≤ 2 * x ^ 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.log_le_iff_le_exp (by linarith), e3]
    linarith
  · have hB : f * (d + f * n + 1) ≤ x * (2 * x ^ 2) := mul_le_mul hfx hA (by linarith) (by linarith)
    rw [Real.log_le_iff_le_exp (by nlinarith), e5]
    nlinarith
  · intro s hs0 hs
    have hfr0 : 0 ≤ f * r := by nlinarith
    have hC : f * r * n ≤ x ^ 3 := by
      have h1 : f * r ≤ x * x := mul_le_mul hfx hrx (by linarith) (by linarith)
      have h2 : f * r * n ≤ x * x * x := mul_le_mul h1 hnx hn0.le (by positivity)
      nlinarith
    rw [Real.log_le_iff_le_exp (by linarith), e3]
    nlinarith

private theorem level_M_eq_g_zero_mul_g_one_of_lawsM {D : D7} (T : Core D) (h : Formalism.L2.Pj.LawsM T) :
    T.Q.l.M = D.host.g 0 * D.host.g 1 := by
  have p := h.pins.2.1
  unfold Formalism.L2.Pj.Par.PinLevel at p
  exact p.1

theorem cusp_data_bounds : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (e : ∀ k : (T.U j σ).Comp, XExt ((T.U j σ).X k)) (M wg : ℝ), 1 ≤ M ∧ Real.log M ≤ 30 * large₂.sc.L ∧ 0 < wg ∧ Real.log wg ≤ 3 * large₂.sc.L ∧ Real.log ((fdeg D.host.E : ℝ) * wg + 2) ≤ 5 * large₂.sc.L ∧ ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤ wg ∧ (∀ v ∈ (e k).L', herm ((T.U j σ).X k).Gm v v = 0 → ∀ b : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc b = b → IsIntegral ℤ b → ∃ γ ∈ ((T.U j σ).X k).Γ, ((T.U j σ).X k).χ (laU (T.U j σ) (wtA w) w.n k) γ = 1 ∧ ∀ τ : ((T.U j σ).X k).Ψ, (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j σ).X k).flowMat v τ ((M : ℂ) * τ.1 b)) ∧ Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L ∧ Real.log (e k).NA ≤ 4 * large₂.sc.L ∧ Real.log (e k).NC ≤ 2 * large₂.sc.L ∧ Real.log (e k).g ≤ 19 * large₂.sc.L ∧ Real.log (1 / (e k).k0) ≤ 3 * large₂.sc.L := by
  intro D T h hGam large₂ j hj w hP hL hrn σ hσ
  obtain ⟨hgi, hlrd, hdd, hcc, -, -, -, hDF, hn⟩ := hP
  obtain ⟨⟨NA, hNA0, hNAi, hNAL⟩, hccA, hcc0, ⟨m, hm0, hmi, hmL⟩, hk0L, hfdeg, -, -, hfr, hf1, hxicc, -,
    hxiabs⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hdd hcc
  have h10 := GlobalTheory.T.modelWeight_size_spread_bound D T h j hj w σ hσ
  obtain ⟨hW1, hW2, hW3⟩ := weight_bounds large₂.sc.L (D.R.f : ℝ) (D.R.r : ℝ) (w.n : ℝ) (WeightAlgebra.DF w : ℝ) hL
    (by exact_mod_cast hf1) (by exact_mod_cast hfr) (by exact_mod_cast hrn) (by positivity) hn hDF
  have hwg0 : 0 < (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := by positivity
  have hwgF : Real.log ((fdeg D.host.E : ℝ) * ((WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1) + 2) ≤ 5 * large₂.sc.L := by
    rw [hfdeg]; exact hW2
  have hspread : ∀ k, (∑ τ, ((T.U j σ).X k).spread (laU (T.U j σ) (wtA w) w.n k) τ) ≤
      (WeightAlgebra.DF w : ℝ) + D.R.f * w.n + 1 := fun k => by linarith [(h10 k).1]
  have hla : ∀ k, Real.log (1 + ∑ τ, ∑ i, |((laU (T.U j σ) (wtA w) w.n k τ i : ℤ) : ℝ)|) ≤ 3 * large₂.sc.L :=
    fun k => hW3 _ (by positivity) (h10 k).2
  rcases isEmpty_or_nonempty (T.U j σ).Comp with hE | ⟨⟨k₁⟩⟩
  · exact ⟨fun k => isEmptyElim k, 1, _, le_rfl, by simp; positivity, hwg0, hW1, hwgF, fun k => isEmptyElim k⟩
  have hPr : GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.Q.l.M :=
    fun k γ h1 h2 => hGam j hj σ hσ k γ h1 h2
  choose Xx hXx hXg hXΛ hXk0 hXNA hXNC using GlobalTheory.T.exists_rankOneCuspLatticeData_of_principal D T.toCore h.toLawsCore j hj σ hσ hPr
  choose e heNA heNC heg hek0 using fun k => exists_ext (Xx k) _ (hXx k) _ (hXΛ k) NA
    (Ideal.absNorm D.host.ccK) hNA0 hcc0 hNAi hccA
  have hMpos : 0 < T.Q.l.M := by rw [← hXg k₁]; exact (Xx k₁).g_pos
  have hlev : T.Q.l.M = D.host.g 0 * D.host.g 1 := level_M_eq_g_zero_mul_g_one_of_lawsM T.toCore h.toLawsCore.toLawsM

  have hgL : Real.log (T.Q.l.M : ℝ) ≤ 19 * large₂.sc.L := by
    have h0 : D.host.g 0 ≠ 0 := fun h0 => by simp [hlev, h0] at hMpos
    have h1 : D.host.g 1 ≠ 0 := fun h1 => by simp [hlev, h1] at hMpos
    rw [hlev, Nat.cast_mul, Real.log_mul (by exact_mod_cast h0) (by exact_mod_cast h1)]
    linarith [hgi 0, hgi 1]

  have hmX : ∀ k, IsIntegral ℤ ((m : D.host.E) * (2 * ((T.U j σ).X k).ξ0)) := by
    intro k
    rcases GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq D.host.E D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
      hxicc ((T.U j σ).X k).ξ0_im (by rw [hxiabs, h.xiAbs j hj σ hσ k]) with h1 | h1
    · rw [h1]; exact hmi
    · rw [h1]; convert hmi.neg using 1; ring
  have hMk : ∀ k, ((e k).toX.g * (e k).toX.NA * (e k).toX.NC * m : ℕ) =
      T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m := by
    intro k
    show (e k).g * (e k).NA * (e k).NC * m = _
    rw [heg, heNA, heNC, hXg]
  have hM1 : 1 ≤ T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hMpos hNA0) hcc0) hm0
  refine ⟨e, ((T.Q.l.M * NA * Ideal.absNorm D.host.ccK * m : ℕ) : ℝ), _, by exact_mod_cast hM1, ?_, hwg0, hW1,
    hwgF, fun k => ⟨hspread k, ?_, hla k, ?_, ?_, ?_, ?_⟩⟩
  · push_cast
    have hN : (0 : ℝ) < NA := by exact_mod_cast hNA0
    have hC : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hcc0
    have hm : (0 : ℝ) < m := by exact_mod_cast hm0
    have hg : (0 : ℝ) < T.Q.l.M := by exact_mod_cast hMpos
    rw [Real.log_mul (by positivity) hm.ne', Real.log_mul (by positivity) hC.ne',
      Real.log_mul hg.ne' hN.ne']
    linarith
  · intro v hv hv0 b hb hbi
    obtain ⟨γ, hγ, hγf⟩ := GlobalTheory.TransvLevel.transv_mem D.host.E D.R.r (e k).toX m (hmX k) v hv hv0 b hb hbi
    refine ⟨γ, hγ, h.chiTriv j hj σ hσ _ _ (Formalism.L2.Pj.dom_wtA w) k γ hγ, fun τ => ?_⟩
    have := hγf τ
    rw [hMk k] at this
    exact this
  · rw [heNA]; exact hNAL
  · rw [heNC]; exact hcc
  · rw [heg, hXg]; exact hgL
  · rw [hek0, hXk0]; exact hk0L

end GlobalTheory.CuspDataBounds
