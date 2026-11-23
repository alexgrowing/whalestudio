import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfQ

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Metric
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem vanish_other (hV : VanishAtSStatement (E := E)) (hM : MeasInvStatement (E := E))
    (hO : OrthoStatement (E := E)) (hLU : LUStatement (E := E)) (hR : NfacRmulStatement (E := E))
    (Xa : ArchInM X) (Fl : FlatM X Xa) (ψ : Frame X.Ψ r → ℝ) (C0 : ℝ) (hψb : ∀ x ∈ X.dom, ψ x ≤ C0)
    (bb : ℝ) (hbb : 0 ≤ bb) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (b0 : Frame X.Ψ r)
    (hb0 : b0 ∈ Bor X.Ψ r) (j : Fin Fl.δ) (hx : Fl.xs j = rmul x0 b0) (ε : ℝ) (hε : 0 < ε)
    (hball : closedBall (0 : V (nd X)) (2 * ε) ⊆ OmF X x0)
    (hiso : ∀ y ∈ closedBall (0 : V (nd X)) (2 * ε), (∀ k, Fl.s k (cpt X x0 y) = 0) → y = 0)
    (hnull : volume {y | y ∈ OmF X x0 ∧ HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y = 0} = 0)
    (F : V (nd X) → ℂ)
    (hI : ∫⁻ y in OmF X x0, ENNReal.ofReal (‖HE.cut ε hε y - F y‖ ^ 2 *
          Real.exp (-psie X x0 Xa.Fp Xa.L ψ bb y) *
          HE.nsq (fun k z => Fl.s k (cpt X x0 z)) y ^ (-(nd X : ℝ))) < ⊤)
    (P : Frame X.Ψ r → ℂ) (hBE : IsBEq X Xa.Fp P) (hPF : ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) (j' : Fin Fl.δ) (hne : γ ≠ 1 ∨ j' ≠ j) :
    P (lact γ (Fl.xs j')) = 0 := by
  have hw0sec : X.IsSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1.1
  have hssec : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hy : lact γ (Fl.xs j') ∈ X.dom := OntoS.dom_lact X hγ (Fl.xs_mem j')
  obtain ⟨x1, ho1, b1, hb1, hyeq⟩ := hO r X _ hy
  have hx1dom : x1 ∈ X.dom := orth_mem_dom X x1 ho1

  have hs1 : ∀ k, Fl.s k x1 = 0 := by
    intro k
    have h0 : Fl.s k (lact γ (Fl.xs j')) = 0 :=
      (Fl.S_eq _ hy).2 ⟨j', γ, hγ, idF X, idF_mem X, by rw [rmul_idF]⟩ k
    rw [hyeq, (hssec k).2.1 x1 hx1dom b1 hb1] at h0
    exact (mul_eq_zero.1 h0).resolve_left (bchar_ne_zero X hb1 _)
  have hw1 : Fl.w0 x1 ≠ 0 := by
    intro h
    have h1 : Fl.w0 (lact γ (Fl.xs j')) = X.χ Xa.L γ * Fl.w0 (Fl.xs j') :=
      hw0sec.2.2 γ hγ _ (Fl.xs_mem j')
    rw [hyeq, hw0sec.2.1 x1 hx1dom b1 hb1, h, mul_zero] at h1
    exact mul_ne_zero (chi_ne X hγ) (Fl.w0_ne j') h1.symm
  have hx0dom : x0 ∈ X.dom := orth_mem_dom X x0 ho
  have hx0d : ∀ τ, (mat x0 τ).det ≠ 0 := fun τ => (hx0dom τ).1
  have hx1d : ∀ τ, (mat x1 τ).det ≠ 0 := fun τ => (hx1dom τ).1
  have hx1av := avoid_base X Xa Fl j j' hγ hne x0 b0 hb0 hx x1 b1 hb1 hyeq ε hball hiso hs1
  obtain ⟨Nb, hNb, hNbav⟩ :=
    nbhd_avoid X x0 hx0d (isCompact_closedBall (0 : V (nd X)) (2 * ε)) hx1av hx1d
  have hOm : IsOpen (OmF X x1) := (isOpen_dom X).preimage (cpt_diff X x1).continuous
  have hS : OmF X x1 ∩ cpt X x1 ⁻¹' Nb ∈ 𝓝 (0 : V (nd X)) := by
    refine Filter.inter_mem (hOm.mem_nhds (zero_mem_OmF X x1 ho1)) ?_
    apply (cpt_diff X x1).continuous.continuousAt.preimage_mem_nhds
    rw [cpt_zero X x1]
    exact hNb
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hS
  have hρ : 0 < δ / 2 := half_pos hδ
  have hcbδ : closedBall (0 : V (nd X)) (δ / 2) ⊆ ball 0 δ :=
    Metric.closedBall_subset_ball (half_lt_self hδ)
  have hcb : closedBall (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 := fun w hw => (hδsub (hcbδ hw)).1
  have hbO : ball (0 : V (nd X)) (δ / 2) ⊆ OmF X x1 :=
    fun w hw => hcb (Metric.ball_subset_closedBall hw)
  have hbN : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nb :=
    fun w hw => (hδsub (hcbδ (Metric.ball_subset_closedBall hw))).2

  obtain ⟨Δ, zOf, bOf, hΔ, -, hzOf, -, hdec, hlast⟩ := hLU r X x1 ho1
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) (δ / 2), cpt X x1 w ∈ Nset X Δ zOf (δ / 2) := by
    intro w hw
    obtain ⟨hΔw, hzw, -⟩ := hlast w (hbO hw) (idF X) (idF_mem X)
    rw [rmul_idF] at hΔw hzw
    show (cpt X x1 w ∈ X.dom ∧ Δ (cpt X x1 w) ≠ 0) ∧ zOf (cpt X x1 w) ∈ ball (0 : V (nd X)) (δ / 2)
    exact ⟨⟨hbO hw, hΔw⟩, by rw [hzw]; exact hw⟩
  have hN2 : ∀ z ∈ OmF X x0, cpt X x0 z ∈ Nset X Δ zOf (δ / 2) →
      z ∉ closedBall (0 : V (nd X)) (2 * ε) := by
    intro z _ hzN hzB
    generalize hxz : cpt X x0 z = x at hzN
    have hzN' : (x ∈ X.dom ∧ Δ x ≠ 0) ∧ zOf x ∈ ball (0 : V (nd X)) (δ / 2) := hzN
    obtain ⟨⟨hxd, hxΔ⟩, hxb⟩ := hzN'
    obtain ⟨-, hbB, hxeq⟩ := hdec x hxd hxΔ
    apply hNbav _ (hbN _ hxb) z hzB (binv X (bOf x)) (binv_mem X hbB)
    calc cpt X x1 (zOf x) = rmul (rmul (cpt X x1 (zOf x)) (bOf x)) (binv X (bOf x)) :=
          (rmul_binv X _ hbB).symm
      _ = rmul x (binv X (bOf x)) := by rw [← hxeq]
      _ = rmul (cpt X x0 z) (binv X (bOf x)) := by rw [hxz]
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have hNopen : IsOpen (Nset X Δ zOf (δ / 2)) :=
    hzOf.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hmeas : Measurable ((Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s)) :=
    (gφ_meas X P hBE.1.continuousOn Xa.Fp Xa.L Fl.s fun k => (hssec k).1.continuousOn).indicator
      hNopen.measurableSet
  have hinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) (rmul x b) =
        (Nset X Δ zOf (δ / 2)).indicator (gφ X P Xa.Fp Xa.L Fl.s) x := by
    classical
    intro x hx b hb
    have hiff := Nset_sat X x1 hdec hlast (δ / 2) hx hb
    by_cases hxN : x ∈ Nset X Δ zOf (δ / 2)
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hiff.2 hxN), if_pos hxN,
        gφ_rmul X hR hBE hssec hx hb]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hxN (hiff.1 h)), if_neg hxN]

  obtain ⟨c1, hc1, hc1le⟩ := rhs_bound X x1 Xa Fl P (Nset X Δ zOf (δ / 2)) (δ / 2) hρ hcb hN1
  have hfin := lhs_finite X x0 ho Xa Fl ψ C0 hψb bb hbb ε hε hnull F hI P hPF
    (Nset X Δ zOf (δ / 2)) hN2
  have heq := hM r X x1 x0 ho1 ho _ hmeas hinv
  have hlt := hc1le.trans_lt (heq.trans_lt hfin)
  have hfinI := ENNReal.lt_top_of_mul_ne_top_right hlt.ne (ENNReal.ofReal_pos.2 hc1).ne'
  have hdet := etale_transfer X hLU hw0sec hssec (Fl.xs_mem j') (Fl.coord j') hγ (idF_mem X) ho1
    hb1 (by rw [rmul_idF]; exact hyeq) hw1
  have hnd : 0 < nd X := by have := Xa.n_ge; omega
  have hP1 : P x1 = 0 :=
    hV r X x1 hnd ho1 hx1dom P Fl.w0 Fl.s (δ / 2) hρ ((comp_cpt_diffOn X hBE.1 x1).mono hbO)
      (fun k => (comp_cpt_diffOn X (hssec k).1 x1).mono hbO)
      ((comp_cpt_diffOn X hw0sec.1 x1).mono hbO) hw1 hs1 hdet hfinI
  rw [hyeq, hBE.2 x1 hx1dom b1 hb1, hP1, mul_zero]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IW
