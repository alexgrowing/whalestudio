import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Metric
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def SatB (X : Data E r) (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)}

theorem satB_sat (x1 : Frame X.Ψ r) (ρ : ℝ) {x : Frame X.Ψ r} (hx : x ∈ SatB X x1 ρ) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : lact γ (rmul x b) ∈ SatB X x1 ρ := by
  obtain ⟨γ', hγ', b', hb', z', hz', rfl⟩ := hx
  refine ⟨γ * γ', X.Γ.mul_mem hγ hγ', rmul b' b,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.mul_mem (X := X) hb' hb, z', hz', ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_rmul, ReciprocityTheory.ChartRestriction.G.AR.Up.IW.lact_lact,
    ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc]

theorem mem_satB_self (x1 : Frame X.Ψ r) {ρ : ℝ} (hρ : 0 < ρ) : x1 ∈ SatB X x1 ρ := by
  have hn : nmat X 0 = fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) := by
    funext τ a c
    simp only [nmat]
    split_ifs with h1 h2
    · rw [Matrix.one_apply_ne (ne_of_lt h1).symm]
      first | rfl | simp | exact PiLp.zero_apply _ _
    · subst h2; exact (Matrix.one_apply_eq a).symm
    · exact (Matrix.one_apply_ne h2).symm
  refine ⟨1, X.Γ.one_mem, fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), ?_, 0, Metric.mem_ball_self hρ, ?_⟩
  · intro τ
    refine ⟨?_, fun a c hca => ?_⟩
    · show Matrix.det (1 : Matrix (Fin r) (Fin r) ℂ) ≠ 0
      simp
    · show (1 : Matrix (Fin r) (Fin r) ℂ) a c = 0
      exact Matrix.one_apply_ne (ne_of_lt hca).symm
  · funext τ a c
    simp [lact, rmul, mat, cpt, hn]
    change x1 τ a c = ((Matrix.of (x1 τ) * (1 : Matrix (Fin r) (Fin r) ℂ)) *
      (1 : Matrix (Fin r) (Fin r) ℂ)) a c
    rw [Matrix.mul_one, Matrix.mul_one]
    rfl

theorem rpow_ofReal_ne_top {a : ℝ} (ha : 0 < a) (y : ℝ) : ENNReal.ofReal a ^ y ≠ ⊤ := by
  rw [ENNReal.ofReal_rpow_of_pos ha]
  exact ENNReal.ofReal_ne_top

theorem inFF_of (hLU : LocalUnfoldBStatement (E := E)) {Xa : ArchInM X} (Fl : FlatM X Xa) (hPD : PropDisc X)
    (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) (FF : Set (V (nd X))) (hFF : IsFundSet X x0 FF)
    (g : Frame X.Ψ r → ℂ) (hg : g ∈ X.SS (Xa.Fp + Xa.T • Xa.L))
    (hint : ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤)
    (hv : VanS X Fl.xs Fl.s (Xa.T - nd X) g) : InFF X x0 (WSk X Xa Fl) FF g := by
  have hsec : X.IsSec (Xa.Fp + Xa.T • Xa.L) g := hg.1.1
  have hGm := Gf_meas Xa Fl hsec.1.continuousOn
  have key : ∀ j, ∃ ρ : ℝ, 0 < ρ ∧ IsOpen (SatB X (Fl.xs j) ρ) ∧
      ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ ball (0 : V (nd X)) ρ,
        cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)}, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    intro j
    obtain ⟨ρV, hρV, hV⟩ := hv j
    obtain ⟨ρ0, hρ0, hL⟩ := hLU r X x0 hx0 hPD FF hFF (Fl.xs j) (Fl.xs_mem j)
    have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
      show cpt X (Fl.xs j) 0 ∈ X.dom
      rw [IW.cpt_zero]
      exact Fl.xs_mem j
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (ExF.isOpen_OmF X (Fl.xs j)) 0 h0
    set ρ := min (min ρV ρ0) (ε / 2) with hρdef
    have hρ : 0 < ρ := lt_min (lt_min hρV hρ0) (by linarith)
    have hρV' : ρ ≤ ρV := (min_le_left _ _).trans (min_le_left _ _)
    have hρ0' : ρ ≤ ρ0 := (min_le_left _ _).trans (min_le_right _ _)
    have hcl : closedBall (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j) :=
      (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hεsub
    obtain ⟨hop, K, hK, hb⟩ := hL ρ hρ hρ0'
    refine ⟨ρ, hρ, hop, ?_⟩
    calc _ ≤ K * ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (cpt X (Fl.xs j) z) :=
          hb _ hGm (fun x hx b hb => Gf_rmul Xa Fl hsec hx hb) (fun γ hγ x hx => Gf_lact Xa Fl hsec hγ hx)
      _ < ⊤ := ENNReal.mul_lt_top hK (ball_finite Fl g j hρ hρV' hV hcl)
  choose ρ hρ hop hfin using key
  set U := ⋃ j, SatB X (Fl.xs j) (ρ j) with hUdef
  have hU : IsOpen U := isOpen_iUnion hop
  have hxs : ∀ j, Fl.xs j ∈ U := fun j => Set.mem_iUnion.2 ⟨j, mem_satB_self _ (hρ j)⟩
  have hsat : ∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U := by
    intro x hx γ hγ b hb
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨j, satB_sat _ _ hj hγ hb⟩
  obtain ⟨K, hK⟩ := Fl.family_le_coords U hU hxs hsat
  set P := {z : V (nd X) | cpt X x0 z ∈ U} with hPdef
  have hPm : MeasurableSet P := ((IW.cpt_diff X x0).continuous.isOpen_preimage _ hU).measurableSet
  set C := ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) with hCdef
  have hC : C ≠ ⊤ := rpow_ofReal_ne_top (by positivity) _
  have hoff : ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤ := by
    calc ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
        ≤ ∫⁻ z in FF \ P, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 := by
          refine setLIntegral_mono' (hFF.1.diff hPm) fun z hz => ?_
          have hzd : cpt X x0 z ∈ X.dom := hFF.2.1 hz.1
          exact Gf_le_off Xa Fl g K hzd (hK _ hzd hz.2)
      _ ≤ ∫⁻ z in FF, C * ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_mono_set Set.diff_subset
      _ = C * ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 :=
          lintegral_const_mul' _ _ hC
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hC) hint
  have hcover : FF ⊆ (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)} := by
    intro z hz
    by_cases hzP : z ∈ P
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hzP
      exact Or.inr (Set.mem_iUnion.2 ⟨j, hz, hj⟩)
    · exact Or.inl ⟨hz, hzP⟩
  show ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 < ⊤
  calc ∫⁻ z in FF, Gf Xa Fl g (cpt X x0 z) ∂muF X x0
      ≤ ∫⁻ z in (FF \ P) ∪ ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_mono_set hcover
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∫⁻ z in ⋃ j, FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := lintegral_union_le _ _ _
    _ ≤ ∫⁻ z in FF \ P, Gf Xa Fl g (cpt X x0 z) ∂muF X x0 + ∑' j, ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
          ∃ z' ∈ ball (0 : V (nd X)) (ρ j), cpt X x0 z = lact γ (rmul (cpt X (Fl.xs j) z') b)},
          Gf Xa Fl g (cpt X x0 z) ∂muF X x0 := add_le_add le_rfl (lintegral_iUnion_le _ _)
    _ < ⊤ := by
      rw [tsum_fintype]
      exact ENNReal.add_lt_top.2 ⟨hoff, ENNReal.sum_lt_top.2 fun j _ => hfin j⟩

theorem ontoWeight_of (hLU : LocalUnfoldBStatement (E := E)) : OntoWeightStatement (E := E) := by
  intro r X Xa Fl hPD _ bb m _ _ hlevi _ x0 hx0 FF hFF
  obtain ⟨k0, z0, hz0, hs0⟩ := exists_s_ne Fl x0 hx0
  refine ⟨PsK Xa Fl, fun z => Fl.s k0 (cpt X x0 z), WSk_metric Xa Fl, WSk_lower Xa Fl,
    IW.comp_cpt_diffOn X (s_diffOn Fl k0) x0, ⟨z0, hz0, hs0⟩, fun z hz => ?_, fun z hz hg1 => ?_,
    fun z hz hg1 ξ => ?_, fun g hg hint hv => ?_⟩
  · exact (PsK_cpt_cdAt Fl x0 k0 hz).contDiffWithinAt
  · exact WSk_eq_exp Xa Fl hz (sums_pos Fl hg1)
  · exact PsK_levi Fl x0 k0 m (hlevi x0 hx0) ⟨hz, hg1⟩ ξ
  · exact inFF_of hLU Fl hPD x0 hx0 FF hFF g hg hint hv

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
