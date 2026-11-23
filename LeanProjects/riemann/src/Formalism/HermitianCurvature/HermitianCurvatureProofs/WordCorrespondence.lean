import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem phi_top_cont (hTC : TopContOn) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h P.r) (hh' : D.IsLocPt h' P.r) (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ)
    (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w) :
    Continuous fun c : ℂ => (B2.zWeight P.k P.T P.T' c : ℂ) * p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
  obtain ⟨δ, hδ, hsmall⟩ := rr_top_small P p F w h h' hh Cb hθ hF hw
  have hcon := hTC Wp Wq P p F w h h' hh hh' Cb hθ hF hw
  rw [continuous_iff_continuousAt]
  intro c0
  by_cases hc0 : P.T * P.T' < Complex.normSq c0
  · have hU : IsOpen {c : ℂ | P.T * P.T' < Complex.normSq c} :=
      isOpen_lt continuous_const Complex.continuous_normSq
    have hR : ContinuousAt (fun c : ℂ => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) c0 :=
      hcon.continuousAt (hU.mem_nhds hc0)
    have hz : ContinuousAt (fun c : ℂ => ((Complex.normSq c - P.T * P.T') ^ (P.k - 1) : ℝ)) c0 :=
      ((Complex.continuous_normSq.sub continuous_const).pow _).continuousAt
    refine ((Complex.continuous_ofReal.continuousAt.comp hz).mul hR).congr ?_
    filter_upwards [hU.mem_nhds hc0] with c hc
    simp only [Pi.mul_apply, Function.comp_apply, B2.zWeight, if_pos (le_of_lt hc)]
  · push Not at hc0
    have hU : IsOpen {c : ℂ | Complex.normSq c - P.T * P.T' < δ} :=
      isOpen_lt (Complex.continuous_normSq.sub continuous_const) continuous_const
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hU.mem_nhds (show Complex.normSq c0 - P.T * P.T' < δ by linarith)] with c hc
    rw [hsmall c hc, mul_zero]

theorem topPart_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (w : List (Letter ℂ S))
    (hTop : TopP P z z' π π' μ L st K w) (hr : P.r = 0) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (K 0) x) (hy : InK (K 0) y) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) :
    Integrable (fun g : Mt P.k P.r => topDens L st w x y c (Matrix.of g)) μ ∧
      ∀ (s : ℂ) (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π')),
        multiplicationOperator Wv (fun _ g => fsv s (P5.zeta P.k P.r z z' g)) → multiplicationOperator Wv' (fun _ g => fsv (-s) (P5.zeta P.k P.r z z' g)) →
        ∫ g : Mt P.k P.r, fsv s (P5.zeta P.k P.r z z' (Matrix.of g)) * topDens L st w x y c (Matrix.of g) ∂μ =
          P5.form μ 0 (P5.act (RRi L st 0 w) (act (Vw (mkP Wv Wv') s w) x)) y c := by
  have hl : (0 : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp [hr])
  rw [hl] at hx hy ⊢
  obtain ⟨hi, hs, -⟩ := hTop x y hx hy c hc
  exact ⟨hi, hs⟩

theorem hsInner_zero_right' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_left]

theorem continuous_fsv (s : ℂ) : Continuous (fun t : ℂ => fsv s t) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj))

theorem pStd_top (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) (hOne : FormOne) (hZN : ZetaNormExists)
    (hTC : TopContOn) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F)
    (hw : KB.CutWord P p.l0 w) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form P.r le_rfl w (KB.waveG (p.T.bs P.r) s w (KB.slv p.T F P.r le_rfl w h hh.2))
          (KB.slv p.T F P.r le_rfl w h' hh'.2) := by
  classical
  obtain ⟨hl1, hlk, hk2⟩ := p.hl
  have hr0 : P.r - P.r = 0 := Nat.sub_self _
  let jF : Fin (P.r + 1) := ⟨P.r, Nat.lt_succ_self _⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := hZN P.k (P.r - P.r) Wp Wq (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  set x := KB.slv p.T F P.r le_rfl w h hh.2 with hxdef
  set x' := KB.slv p.T F P.r le_rfl w h' hh'.2 with hx'def
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (x' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := nice_common (p.T.bs P.r) hcx
  obtain ⟨ε₂, hε₂, hx'⟩ := nice_common (p.T.bs P.r) hcx'
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hxn : ∀ e, JC.NiceCoef (p.T.bs P.r) ε (x e) := fun e =>
    ⟨(hx e).1, (hx e).2.1, fun g hg h0 => le_trans (min_le_left _ _) ((hx e).2.2 g hg h0)⟩
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs P.r) ε (x' e) := fun e =>
    ⟨(hx' e).1, (hx' e).2.1, fun g hg h0 => le_trans (min_le_right _ _) ((hx' e).2.2 g hg h0)⟩
  choose Φ hΦK hΦ using fun a => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx a)
  choose Φ' hΦ'K hΦ' using fun a => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' a)
  have hHTa := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'

  let c0 : Fin (JC.parLev P jF).r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX (JC.parLev P jF).r := fun _ => one_ne_zero
  obtain ⟨hint, hs⟩ := topPart_zero (JC.parLev P jF) _ _ _ _ μ L st K (D.positionted w) (hThm (D.positionted w) hwOK).1 hr0
    Φ Φ' hΦK hΦ'K c0 hc0
  have hTz : Tz P.k (P.r - P.r) (p.T.bs P.r).z = P.T := hPl.2.2.2.1
  have hTz' : Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T' := hPl.2.2.2.2.1

  set R : ℂ → ℂ := fun c => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) with hRdef
  set U : Set ℂ := {c | P.T * P.T' < Complex.normSq c} with hUdef
  set ψ : ℂ → ℂ := U.piecewise R 0 with hψdef
  have hRc : ContinuousOn R U := hTC Wp Wq P p F w h h' hh hh' Cb hθ hF hw
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_normSq
  have hψm : Measurable ψ := hRc.measurable_piecewise continuousOn_const hUo.measurableSet
  have hae : ∀ᵐ g ∂μ, topDens L st (D.positionted w) Φ Φ' c0 (Matrix.of g) =
      ψ (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem hμ.1] with g hg
    by_cases hG : 0 < GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of g)
    · have hdom : (c0, Matrix.of g) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨hc0, hg, hG⟩
      rw [hHTa (c0, Matrix.of g) hdom]
      have hU' : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g) ∈ U := by
        unfold GGl at hG
        rw [hTz, hTz'] at hG
        show P.T * P.T' < _
        linarith
      rw [hψdef, Set.piecewise_eq_of_mem _ _ _ hU']
      rfl
    · have hnd : (c0, Matrix.of g) ∉ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := fun hd => hG hd.2.2
      have hU' : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g) ∉ U := by
        intro hm
        apply hG
        unfold GGl
        rw [hTz, hTz']
        have : P.T * P.T' < _ := hm
        linarith
      rw [hψdef, Set.piecewise_eq_of_notMem _ _ _ hU']
      unfold topDens
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [(act (Fr.ofWord L st (D.positionted w)).F Φ' e).2.1 (c0, Matrix.of g) hnd, hsInner_zero_right']

  set φ : ℂ → ℂ := fun c => (KB.levW P (P.r + 1) c : ℂ) * R c with hφdef
  have hlev : ∀ c, KB.levW P (P.r + 1) c = B2.zWeight P.k P.T P.T' c := fun c => by simp [KB.levW]
  have hφψ : ∀ c, (B2.zWeight P.k P.T P.T' c : ℂ) * ψ c = φ c := by
    intro c
    rw [hφdef]
    simp only [hlev]
    by_cases hc : c ∈ U
    · rw [hψdef, Set.piecewise_eq_of_mem _ _ _ hc]
    · rw [hψdef, Set.piecewise_eq_of_notMem _ _ _ hc]
      have hz : B2.zWeight P.k P.T P.T' c = 0 := by
        unfold B2.zWeight
        split_ifs with hle
        · have hcU : ¬ P.T * P.T' < Complex.normSq c := hc
          have he : Complex.normSq c - P.T * P.T' = 0 := by linarith
          rw [he, zero_pow (by omega)]
        · rfl
      rw [hz]; simp
  refine ⟨φ, ?_, ?_, fun c _ => rfl, fun s => ?_⟩
  · exact (phi_top_cont hTC P p F w h h' hh hh' Cb hθ hF hw).congr fun c => by rw [hφdef]; simp only [hlev]; rfl
  · have hi := zetaNorm_integrable hμ ψ hψm (hint.congr hae)
    rw [hTz, hTz'] at hi
    exact hi.congr (Filter.Eventually.of_forall hφψ)
  · obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π
      (p.T.bs jF).π' (-s)
    have key := hs s Wv Wv' hW hW'
    have hm : ∀ y ∈ DomR P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - P.r) → ℂ) (g : Mx P.k (P.r - P.r)) => fsv s (P5.zeta P.k (P.r - P.r) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - P.r) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_top_eq_zeta hr0]
    have hΨ := Formalism.FourierDecayAlt.P.PBFV.radPic_wave (p.T.bs jF) ε s w x hxn Φ hΦ _ (by omega) hm Wv Wv' hW
    have hnx := Formalism.FourierDecayAlt.P.PBFV.waveG_nice (p.T.bs P.r) ε s w x hxn
    have hform := hOne Wp Wq P p.T jF X μ L st p.l0 hD hμ w _ _ _ _ ε hε hnx hxn' hΨ hΦ'
    have hmeas : Measurable fun ζ => fsv s ζ * ψ ζ := (continuous_fsv s).measurable.mul hψm
    have hlaw := zetaNorm_integral hμ (fun ζ => fsv s ζ * ψ ζ) hmeas
    rw [hTz, hTz'] at hlaw
    calc ∫ c, fsv s c * φ c = ∫ ζ, (B2.zWeight P.k P.T P.T' ζ : ℂ) * (fsv s ζ * ψ ζ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
          simp only []
          rw [← hφψ c]; ring
      _ = ∫ g, fsv s (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) *
            ψ (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) ∂μ := hlaw.symm
      _ = ∫ g, fsv s (P5.zeta P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of g)) *
            topDens L st (D.positionted w) Φ Φ' c0 (Matrix.of g) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with g hg
          rw [hg]; rfl
      _ = P5.form μ 0 (P5.act (RRi L st 0 (D.positionted w)) (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ)) Φ' c0 := key
      _ = P5.form μ 0 (P5.act (RRi L st 0 (D.positionted w)) (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ)) Φ' 0 :=
          Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ 0
      _ = _ := hform.symm

theorem pStd_belowC (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hOne : FormOne) (hZN : ZetaNormExists)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (hjr : j < P.r) (w : List C.Letter)
    (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (hF : KB.CptCoef p.T.base F)
    (hw : KB.CutWord P p.l0 w) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) := by
  obtain ⟨hl1, hlk, -⟩ := p.hl
  have hr : 0 < P.r - j := by omega
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := hZN P.k (P.r - j) Wp Wq (p.T.bs j)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2

  set x := KB.slv p.T F j hj w h hh.2 with hxdef
  set x' := KB.slv p.T F j hj w h' hh'.2 with hx'def
  have hcx : ∀ e, KB.CptCoef (p.T.bs j) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs j) (x' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h' hh' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := nice_common (p.T.bs j) hcx
  obtain ⟨ε₂, hε₂, hx'⟩ := nice_common (p.T.bs j) hcx'
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)}, ε ≤ ε' → JC.NiceCoef (p.T.bs j) ε' G →
      JC.NiceCoef (p.T.bs j) ε G := fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e) := fun e => mono (min_le_right _ _) (hx' e)
  choose Φ hΦK hΦ using fun a => pic_cpt (p.T.bs j) (K 0) hJ (hcx a)
  choose Φ' hΦ'K hΦ' using fun a => pic_cpt (p.T.bs j) (K 0) hJ (hcx' a)

  have hstep := (hThm (D.positionted w) hwOK).2.1 ⟨0, hr⟩
  have hl : (⟨0, hr⟩ : Fin (JC.parLev P jF).r).castSucc = 0 := Fin.ext rfl
  unfold StepP at hstep
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hCφ⟩, hφs⟩ := hstep Φ Φ' (fun a => hΦK a)
    (fun a => hΦ'K a) (fun _ => 1) (fun _ => one_ne_zero)
  refine ⟨φ, hφc, integrable_of_decay4 hφc hCφ, fun c hc => ?_, fun s => ?_⟩
  · rw [hφ c hc]
    exact hRH Wp Wq P p F j (by omega) w h h' hh hh' X μ L st Φ Φ' hD hμ hF hw hΦ hΦ' c hc
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := Formalism.FourierDecayAlt.P.PBFV.radPic_wave (p.T.bs jF) ε s w x hxn Φ hΦ _ (by omega) hm Wv Wv' hW
    have hnx := Formalism.FourierDecayAlt.P.PBFV.waveG_nice (p.T.bs j) ε s w x hxn
    rw [hφs s Wv Wv' hW hW']
    show _ = D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) x'
    rw [hOne Wp Wq P p.T jF X μ L st p.l0 hD hμ w _ _ _ _ ε hε hnx hxn' hΨ hΦ']
    unfold RRform
    exact Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ 0

theorem pStd_of_cpt (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne)
    (hZN : ZetaNormExists) (hTC : TopContOn) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' Cb hθ hF hw
  by_cases hjr : j < P.r
  · exact pStd_belowC hP hRH hOne hZN P p F j hj hjr w h h' hh hh' hF hw
  · have e : j = P.r := by omega
    subst e
    exact pStd_top hP hHT hOne hZN hTC P p F w h h' hh hh' Cb hθ hF hw

theorem pStd_of (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne) (hZN : ZetaNormExists)
    (hTC : TopContOn) : KB.PStd := by
  intro hP
  refine pStd_of_cpt ?_ hRH hHT hOne hZN hTC
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  obtain ⟨K, h1, h2, h3, h4⟩ := hP Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
  exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩

end Formalism.FourierDecayAlt.P.PBO
