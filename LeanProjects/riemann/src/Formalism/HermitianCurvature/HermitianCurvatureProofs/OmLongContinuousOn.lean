import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

open MeasureTheory Filter Topology Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

section last

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem lastBlock_decay (β : ℂ) (p s : ℕ) (hs : 1 ≤ s) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) (Ψ : G.Mat (p + s) → V) (hΨ : PBJ.KCls Ψ) (a : ℝ) :
    ∃ K : ℝ, Continuous (U.PhiTop (p := p) (s := s) β σ d Ψ) ∧
      ∀ Z, ‖U.PhiTop (p := p) (s := s) β σ d Ψ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a) := by
  set N : ℝ := ((p + s : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast (by omega : 0 < p + s)
  set E : ℝ := 5 * N * (|a| + 2 * N ^ 2 + 1) with hE
  have hEq : E / (5 * N) = |a| + 2 * N ^ 2 + 1 := by
    rw [hE]; field_simp
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  obtain ⟨Cst, hC⟩ := Formalism.FourierDecayAlt.P.top_cells p s β σ d hd hs 0 (fun _ => E) (by
    intro i _
    rw [← hN, hEq]
    have := abs_nonneg a
    linarith)
  obtain ⟨K, hK⟩ := PBJ.Asm.decayAll_of_cls Ψ hΨ 0 E hE0
  obtain ⟨-, hD⟩ := hC V Ψ K hK
  refine ⟨Cst * K, hD.1.continuous, fun Z => ?_⟩
  have h := hD.2 0 le_rfl Z
  rw [norm_iteratedFDeriv_zero] at h
  simp only at h
  rw [← hN, hEq] at h
  have h1 : (1 : ℝ) ≤ 1 + ‖Z‖ := by linarith [norm_nonneg Z]
  have hpos : 0 < (1 + ‖Z‖) ^ (-(|a| + 2 * N ^ 2 + 1)) := Real.rpow_pos_of_pos (by linarith) _
  have hCK : 0 ≤ Cst * K := by
    by_contra hneg
    have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hpos
    linarith [norm_nonneg (U.PhiTop (p := p) (s := s) β σ d Ψ Z)]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hCK)
  apply Real.rpow_le_rpow_of_exponent_le h1
  have := le_abs_self a
  nlinarith [sq_nonneg N]

theorem vec_rep (β : ℂ) (hβ : β ≠ 0) {n : ℕ} (Ψ : G.Mat n → V) (hΨ : PBJ.KCls Ψ) (h : C.LPt)
    (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hn : D.ptSize h + (m + 1) = n) :
    ∃ (κ : ℂ) (Ψ' : G.Mat (m + 1) → V), κ ≠ 0 ∧
      (∀ a : ℝ, ∃ K : ℝ, Continuous Ψ' ∧ ∀ Z, ‖Ψ' Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) ∧
      ∀ c : ℂ, c ≠ 0 → ∀ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN (h ++ [(m + 1, c)]) n →
        U.PhiTop (p := n) (s := 0) β σ d Ψ (fun x => x.elim0) = κ • G.OmLong β m Ψ' c := by
  subst hn
  obtain ⟨σh, dh, hdh, hMh⟩ := PBJ.Asm.exists_hMat h hh
  obtain ⟨κ, hκ, hL⟩ := PBJ.long_orbital_integral_multiple β hβ m
  refine ⟨κ⁻¹, U.PhiTop (p := D.ptSize h) (s := m + 1) β σh dh Ψ, inv_ne_zero hκ,
    fun a => lastBlock_decay β _ _ (by omega) σh dh hdh Ψ hΨ a, ?_⟩
  intro c hc σ d hM
  have hMb : U.hMat (Fin.revPerm : Equiv.Perm (Fin (m + 1))) (fun _ => c) =
      D.ptMatN [(m + 1, c)] (D.ptSize [(m + 1, c)]) := by
    rw [PBJ.Asm.hMat_rev]; exact (PBJ.Asm.ptMatN_long (m + 1) c).symm
  have hM' : U.hMat σ d = U.blk2 (U.hMat σh dh) 0 0 (U.hMat Fin.revPerm (fun _ => c)) := by
    rw [hM, hMh, hMb]; exact PBJ.Asm.ptMatN_append h [(m + 1, c)]
  rw [PBJ.fubini_head_last_part β (D.ptSize h) (m + 1) σ d σh dh Fin.revPerm (fun _ => c) V Ψ hdh (fun _ => hc) hM' hΨ]
  have hz := hL Fin.revPerm (fun _ => c) c V (U.PhiTop (p := D.ptSize h) (s := m + 1) β σh dh Ψ) hc
    (PBJ.Asm.hMat_rev _ c)
  rw [hz, smul_smul, inv_mul_cancel₀ hκ, one_smul]

theorem omLong_continuousOn (β : ℂ) (m : ℕ) (Ψ : G.Mat (m + 1) → V) (hΨc : Continuous Ψ) (K a : ℝ)
    (ha : 2 * (((m : ℝ) + 1) * ((m : ℝ) + 1)) < a) (hK : ∀ Z, ‖Ψ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) :
    ContinuousOn (G.OmLong β m Ψ) {0}ᶜ := by
  intro c0 hc0
  have hc0' : c0 ≠ 0 := hc0
  have hn0 : 0 < ‖c0‖ := norm_pos_iff.mpr hc0'
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  refine ContinuousAt.continuousWithinAt ?_
  unfold G.OmLong
  set μ := G.muPi β (G.UT (m + 1)) with hμ
  have hfin : (Module.finrank ℝ (G.UT (m + 1) → ℂ) : ℝ) < a := by
    have e : Module.finrank ℝ (G.UT (m + 1) → ℂ) = Fintype.card (G.UT (m + 1)) * 2 := by
      rw [Module.finrank_pi_fintype]
      simp [Complex.finrank_real_complex]
    have hcard : Fintype.card (G.UT (m + 1)) ≤ (m + 1) * (m + 1) := by
      have := Fintype.card_subtype_le (fun p : Fin (m + 1) × Fin (m + 1) => p.1 < p.2)
      simpa [Fintype.card_prod, Fintype.card_fin] using this
    have hcardR : ((Fintype.card (G.UT (m + 1)) * 2 : ℕ) : ℝ) ≤ 2 * (((m : ℝ) + 1) * ((m : ℝ) + 1)) := by
      have : Fintype.card (G.UT (m + 1)) * 2 ≤ 2 * ((m + 1) * (m + 1)) := by omega
      exact_mod_cast this
    rw [e]; exact lt_of_le_of_lt hcardR ha
  set L : ℝ := (min 1 (‖c0‖ / 2)) ^ (-a) with hL
  have hψc : Continuous (fun v : G.UT (m + 1) → ℂ => G.psi β (G.superSum (G.upper v))) := by
    have h1 : Continuous fun v : G.UT (m + 1) → ℂ => G.superSum (G.upper v) := by
      unfold G.superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper)
    unfold G.psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul h1))))
  have hjoint : Continuous (fun q : ℂ × (G.UT (m + 1) → ℂ) =>
      G.psi β (G.superSum (G.upper q.2)) • Ψ (G.ptLong (m + 1) q.1 * G.upper q.2)) := by
    refine (hψc.comp continuous_snd).smul (hΨc.comp ?_)
    show Continuous fun q : ℂ × (G.UT (m + 1) → ℂ) => G.ptLong (m + 1) q.1 * G.upper q.2
    unfold G.ptLong
    exact (continuous_fst.smul continuous_const).matrix_mul (Formalism.FourierDecayAlt.P.Dx2.SL.cont_upper.comp continuous_snd)
  have hint : Integrable (fun v : G.UT (m + 1) → ℂ => |K| * L * (1 + ‖v‖) ^ (-a)) μ := by
    rw [hμ, PBJ.Om.muPi_eq]
    apply Integrable.smul_measure_nnreal
    exact (integrable_one_add_norm hfin).const_mul _
  refine continuousAt_of_dominated (bound := fun v => |K| * L * (1 + ‖v‖) ^ (-a)) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun x =>
      (hjoint.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · have hball : ∀ᶠ x in 𝓝 c0, ‖c0‖ / 2 < ‖x‖ := by
      have : ContinuousAt (fun x : ℂ => ‖x‖) c0 := continuous_norm.continuousAt
      exact this.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hball] with x hx
    refine Eventually.of_forall fun v => ?_
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hx; linarith
    rw [norm_smul, Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.norm_psi, one_mul]
    have h1 := hK (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v)
    have h2 : (1 + ‖Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v‖) ^ (-a) ≤
        (min 1 ‖x‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv_decay m hx0 v ha0
    have h3 : (min 1 ‖x‖) ^ (-a) ≤ L := by
      rw [hL]
      apply Real.rpow_le_rpow_of_nonpos (by positivity) (min_le_min_left _ hx.le) (by linarith)
    have hv : 0 ≤ (1 + ‖v‖) ^ (-a) := Real.rpow_nonneg (by positivity) _
    show ‖Ψ (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v)‖ ≤ _
    calc ‖Ψ (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v)‖ ≤ K * (1 + ‖Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v‖) ^ (-a) := h1
      _ ≤ |K| * (1 + ‖Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv m x v‖) ^ (-a) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg (by positivity) _)
      _ ≤ |K| * ((min 1 ‖x‖) ^ (-a) * (1 + ‖v‖) ^ (-a)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
      _ ≤ |K| * (L * (1 + ‖v‖) ^ (-a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hv) (abs_nonneg K)
      _ = |K| * L * (1 + ‖v‖) ^ (-a) := by ring
  · exact Eventually.of_forall fun v =>
      (hjoint.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt

end last

section vec

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecV_continuousOn (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef p.T.base F) (h : C.LPt) (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (hsz : D.ptSize h + m = P.r + 1) :
    ContinuousOn (fun c : ℂ => p.V F (h ++ [(m, c)])) {0}ᶜ := by
  obtain ⟨Φ0, hs, hc, hdet, hV⟩ := Formalism.FourierDecayAlt.P.phi_zero_hermitian_curvature Wp Wq P p F hF
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hβ : U.betaU ≠ 0 := Formalism.FourierDecayAlt.P.scale_matching.2.1
  obtain ⟨κ, Ψ', -, hdec, hrep⟩ := vec_rep U.betaU hβ Φ0 ⟨hs, hc, hdet⟩ h hh m' hsz
  set a : ℝ := 2 * (((m' : ℝ) + 1) * ((m' : ℝ) + 1)) + 1 with ha
  obtain ⟨K, hΨc, hK⟩ := hdec a
  have hOm := omLong_continuousOn U.betaU m' Ψ' hΨc K a (by rw [ha]; linarith) hK
  refine (hOm.const_smul κ).congr ?_
  intro c hc0
  have hc0' : c ≠ 0 := hc0
  have hloc : D.IsLocPt (h ++ [(m' + 1, c)]) (P.r + 1) := by
    refine ⟨?_, ?_⟩
    · intro b hb
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hh b hb
      · exact ⟨by omega, hc0'⟩
    · rw [PBJ.Asm.ptSize_append, PBJ.Asm.ptSize_single]; exact hsz
  obtain ⟨σ, d, hM⟩ : ∃ (σ : Equiv.Perm (Fin (P.r + 1))) (d : Fin (P.r + 1) → ℂ),
      U.hMat σ d = D.ptMatN (h ++ [(m' + 1, c)]) (P.r + 1) := by
    have key : ∀ n, D.ptSize (h ++ [(m' + 1, c)]) = n →
        ∃ (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ), U.hMat σ d = D.ptMatN (h ++ [(m' + 1, c)]) n := by
      intro n hn
      subst hn
      obtain ⟨σ, d, -, hM⟩ := PBJ.Asm.exists_hMat (h ++ [(m' + 1, c)]) hloc.1
      exact ⟨σ, d, hM⟩
    exact key _ hloc.2
  show p.V F (h ++ [(m' + 1, c)]) = κ • G.OmLong U.betaU m' Ψ' c
  rw [hV _ σ d hloc hM]
  exact hrep c hc0' σ d hM

end vec

end Formalism.FourierDecayAlt.P.LastBlockContinuity

namespace Formalism.FourierDecayAlt.P.LastBlockContinuity

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section pt

theorem ptEntry_cont (h : C.LPt) (m : ℕ) : ∀ a b : ℕ, Continuous fun c : ℂ => D.ptEntry (h ++ [(m, c)]) a b := by
  induction h with
  | nil =>
    intro a b
    simp only [List.nil_append, D.ptEntry]
    split_ifs <;> first | exact continuous_id | exact continuous_const
  | cons x t ih =>
    intro a b
    obtain ⟨s, u⟩ := x
    simp only [List.cons_append, D.ptEntry]
    split_ifs <;> first | exact continuous_const | exact ih _ _

theorem ptMatN_cont (h : C.LPt) (m n : ℕ) : Continuous fun c : ℂ => D.ptMatN (h ++ [(m, c)]) n :=
  continuous_pi fun a => continuous_pi fun b => ptEntry_cont h m a b

theorem ptG_cont (TT : ℝ) (r : ℕ) (h : C.LPt) (m : ℕ) : Continuous fun c : ℂ => D.ptG TT r (h ++ [(m, c)]) := by
  unfold D.ptG
  exact (Complex.continuous_normSq.comp (ptMatN_cont h m (r + 1)).matrix_det).sub
    (continuous_const.mul (Complex.continuous_normSq.comp (ptMatN_cont h m r).matrix_det))

theorem dH_continuousAt (P : M.Par) (l0 : ℕ) (TT : ℝ) (w : List C.Letter) (h : C.LPt) (m : ℕ)
    (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) (c0 : ℂ) (hG : D.ptG TT P.r (h ++ [(m, c0)]) ≠ 0) :
    ContinuousAt (fun c : ℂ => Top.dH P l0 TT w (h ++ [(m, c)]) e ρ) c0 := by
  unfold Top.dH Top.wPt
  have h1 : ContinuousAt (fun c : ℂ => Complex.normSq (D.ptMatN (h ++ [(m, c)]) (P.r + 1)).det /
      D.ptG TT P.r (h ++ [(m, c)])) c0 :=
    ((Complex.continuous_normSq.comp (ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt).div
      (ptG_cont TT P.r h m).continuousAt hG
  exact Real.continuous_sqrt.continuousAt.comp ((h1.pow _).mul continuousAt_const)

end pt

section zero

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem vecV_eq_zero_of_lt (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hF : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g)
    (hq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q < ε) : D.vecV Bs ν' m₀ F q = 0 := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have hlt : Gf k r Bs.z Bs.z' h'.choose < ε := by rw [← hGq]; exact hq
      have e := P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) F F 0 (by
        filter_upwards [P.B5.ae_inSS Bs] with p hp
        have hz : F (B.sgs p h'.choose) = 0 := by
          by_contra hne
          have := hF _ (P.B7.sgs_mem Bs hp hγ) hne
          rw [P.JCx1.needs.gf_sgs Bs hp] at this
          linarith
        simp [D.orbIntegrand, B.rho, hz])
      rw [e, zero_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end zero

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem smulV_continuousAt (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef p.T.base F) (h : C.LPt) (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (hsz : D.ptSize h + m = P.r + 1) (f : ℂ → ℝ) (A : Wp →L[ℂ] Wp) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hf : 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (h ++ [(m, c0)]) → ContinuousAt f c0) :
    ContinuousAt (fun c : ℂ => ((f c : ℝ) : ℂ) • A.comp (p.V F (h ++ [(m, c)]))) c0 := by
  obtain ⟨hF1, hF2, ε, hε, hFε⟩ := hF
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  rcases lt_or_ge (D.ptG TT P.r (h ++ [(m, c0)])) ε with hlt | hle
  · have hev : ∀ᶠ c in 𝓝 c0, D.ptG TT P.r (h ++ [(m, c)]) < ε :=
      (ptG_cont TT P.r h m).continuousAt.eventually (Iio_mem_nhds hlt)
    refine (continuousAt_const (y := (0 : Wq →L[ℂ] Wp))).congr ?_
    filter_upwards [hev] with c hc
    have h0 : p.V F (h ++ [(m, c)]) = 0 := vecV_eq_zero_of_lt p.T.base p.ν' p.m₀ _ hFε hc
    rw [h0, ContinuousLinearMap.comp_zero, smul_zero]
  · have hpos : 0 < D.ptG TT P.r (h ++ [(m, c0)]) := lt_of_lt_of_le hε hle
    have hV : ContinuousAt (fun c : ℂ => p.V F (h ++ [(m, c)])) c0 :=
      (vecV_continuousOn P p F ⟨hF1, hF2, ε, hε, hFε⟩ h hh m hm hsz).continuousAt
        (isOpen_compl_singleton.mem_nhds hc0)
    exact (Complex.continuous_ofReal.continuousAt.comp (hf hpos)).smul (continuousAt_const.clm_comp hV)

theorem hsV_continuousOn (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef p.T.base F) (h h' : C.LPt) (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0) (hh' : ∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0)
    (m : ℕ) (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1) (hsz' : D.ptSize h' + m = P.r + 1) :
    ContinuousOn (fun cc : ℂ × ℂ => B.hsInner (p.V F (h ++ [(m, cc.1)])) (p.V F (h' ++ [(m, cc.2)])))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  rintro ⟨c, c'⟩ ⟨hc, hc'⟩
  have h1 := (vecV_continuousOn P p F hF h hh m hm hsz).continuousAt (isOpen_compl_singleton.mem_nhds hc)
  have h2 := (vecV_continuousOn P p F hF h' hh' m hm hsz').continuousAt (isOpen_compl_singleton.mem_nhds hc')
  exact (Formalism.FourierDecayAlt.P.B6.hsInner_continuous.continuousAt.comp
    ((ContinuousAt.comp (x := (c, c')) h1 continuous_fst.continuousAt).prodMk
      (ContinuousAt.comp (x := (c, c')) h2 continuous_snd.continuousAt))).continuousWithinAt

theorem topOf_continuousOn (P : M.Par) (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef p.T.base F) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (w : List C.Letter)
    (hw : KB.CutWord P p.l0 w) (h h' : C.LPt) (hh : ∀ b ∈ h, 1 ≤ b.1 ∧ b.2 ≠ 0)
    (hh' : ∀ b ∈ h', 1 ≤ b.1 ∧ b.2 ≠ 0) (m : ℕ) (hm : 1 ≤ m) (hsz : D.ptSize h + m = P.r + 1)
    (hsz' : D.ptSize h' + m = P.r + 1) :
    ContinuousOn (fun cc : ℂ × ℂ => Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (h ++ [(m, cc.1)]) (h' ++ [(m, cc.2)]))
      (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) := by
  unfold Top.topOf
  refine continuousOn_finsetSum _ fun e _ => continuousOn_finsetSum _ fun ρ _ => ?_
  obtain ⟨F', hF', -, hV⟩ := Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  rintro ⟨c, c'⟩ ⟨hc, hc'⟩
  have hX := smulV_continuousAt P p F' hF' h hh m hm hsz (fun c => Top.dH P p.l0 TT w (h ++ [(m, c)]) e ρ)
    (p.TP.E ρ) c hc (fun hpos => dH_continuousAt P p.l0 TT w h m e ρ c hpos.ne')
  have hY := smulV_continuousAt P p F' hF' h' hh' m hm hsz' (fun c => Top.dH P p.l0 TT w (h' ++ [(m, c)]) e ρ)
    (p.TP.E ρ) c' hc' (fun hpos => dH_continuousAt P p.l0 TT w h' m e ρ c' hpos.ne')
  have hcont := Formalism.FourierDecayAlt.P.B6.hsInner_continuous.continuousAt.comp
    ((ContinuousAt.comp (x := (c, c')) hX continuous_fst.continuousAt).prodMk
      (ContinuousAt.comp (x := (c, c')) hY continuous_snd.continuousAt))
  refine (hcont.congr (Eventually.of_forall fun x => ?_)).continuousWithinAt
  simp only [Function.comp]
  have e1 : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(m, x.1)]) = p.V F' (h ++ [(m, x.1)]) := hV _
  have e2 : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h' ++ [(m, x.2)]) = p.V F' (h' ++ [(m, x.2)]) := hV _
  rw [e1, e2, Formalism.FourierDecayAlt.P.B6.hsInner_smul_left, Formalism.FourierDecayAlt.P.B6.hsInner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

end top

end Formalism.FourierDecayAlt.P.LastBlockContinuity
