import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.EvQTrJBFF
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.NFFinal
import CompanionTheory.AutomorphicTheory.JacobiDiagonalBounds.Vander
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreNS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.MainStatements.NFTie

namespace Formalism.FourierDecayAlt.P.NormalFormRelations

noncomputable section

theorem opOrder_le {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {o : ℕ} (Dop : B.DiffOp k r Wp Wq)
    (h : ∀ T ∈ Dop, T.word.length ≤ o) : B.opOrder Dop ≤ o := by
  induction Dop with
  | nil => exact Nat.zero_le _
  | cons T l ih => exact max_le (h T List.mem_cons_self) (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))

theorem thr_arith (CcL Cb R x W o s d A : ℝ) (hR : 0 ≤ R) (hx : 1 ≤ x) (hW : 0 ≤ W) (ho : o ≤ Cb * W * x)
    (hs : s ≤ o) (hd : d ≤ o) (hA : (|CcL| + 12 + 8 * |Cb|) * (R + 1) ^ 4 * (W * x ^ 2 + x ^ 3) ≤ A) :
    CcL * (R + 1) ^ 4 * (W * x ^ 2 + x ^ 3) ≤ A ∧ 12 * (R + 1) * x ^ 2 + 6 * R * d + 0 ≤ A - (2 * R + 2) * s := by
  have h1 : 1 ≤ R + 1 := by linarith
  have h4 : R + 1 ≤ (R + 1) ^ 4 := by simpa using pow_le_pow_right₀ h1 (show 1 ≤ 4 by norm_num)
  have hx2 : x ≤ x ^ 2 := by simpa using pow_le_pow_right₀ hx (show 1 ≤ 2 by norm_num)
  have hx3 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (show 2 ≤ 3 by norm_num)
  have hx0 : 0 ≤ x := by linarith
  have hWx : 0 ≤ W * x := mul_nonneg hW hx0
  have hT0 : 0 ≤ (R + 1) ^ 4 * (W * x ^ 2 + x ^ 3) := by positivity
  have t1 : (R + 1) * x ^ 2 ≤ (R + 1) ^ 4 * (W * x ^ 2 + x ^ 3) :=
    mul_le_mul h4 (by nlinarith [mul_nonneg hW (sq_nonneg x)]) (by positivity) (by positivity)
  have t2 : (R + 1) * (W * x) ≤ (R + 1) ^ 4 * (W * x ^ 2 + x ^ 3) :=
    mul_le_mul h4 (by nlinarith [mul_le_mul_of_nonneg_left hx2 hW, pow_nonneg hx0 3]) hWx (by positivity)
  have ho' : o ≤ |Cb| * (W * x) := by
    rw [mul_assoc] at ho
    exact le_trans ho (mul_le_mul_of_nonneg_right (le_abs_self _) hWx)
  have hob : 0 ≤ |Cb| * (W * x) := by positivity
  have t3 : (R + 1) * (|Cb| * (W * x)) ≤ |Cb| * ((R + 1) ^ 4 * (W * x ^ 2 + x ^ 3)) := by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left t2 (abs_nonneg _)
  have u1 : R * d ≤ (R + 1) * (|Cb| * (W * x)) :=
    le_trans (mul_le_mul_of_nonneg_left (le_trans hd ho') hR) (mul_le_mul_of_nonneg_right (by linarith) hob)
  have u2 : (R + 1) * s ≤ (R + 1) * (|Cb| * (W * x)) := mul_le_mul_of_nonneg_left (le_trans hs ho') (by linarith)
  have v1 : CcL * ((R + 1) ^ 4 * (W * x ^ 2 + x ^ 3)) ≤ |CcL| * ((R + 1) ^ 4 * (W * x ^ 2 + x ^ 3)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hT0
  have v2 : 0 ≤ |CcL| * ((R + 1) ^ 4 * (W * x ^ 2 + x ^ 3)) := by positivity
  have v3 : 0 ≤ |Cb| * ((R + 1) ^ 4 * (W * x ^ 2 + x ^ 3)) := by positivity
  constructor <;> nlinarith

theorem sum_trunc {E : Type} [AddCommGroup E] [Module ℂ E] {Q o : ℕ} (x : ℂ) (v : Fin (Q + 1) → E)
    (hv : ∀ q : Fin (Q + 1), o < q → v q = 0) :
    ∑ q : Fin (Q + 1), x ^ (q : ℕ) • v q =
      ∑ j : Fin (o + 1), x ^ (j : ℕ) • (if h : (j : ℕ) < Q + 1 then v ⟨j, h⟩ else 0) := by
  rw [← nf_sum_pad (M := Q + 1 + (o + 1)) (by omega) x v, ← nf_sum_pad (M := Q + 1 + (o + 1)) (by omega) x
    fun j : Fin (o + 1) => if h : (j : ℕ) < Q + 1 then v ⟨j, h⟩ else 0]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  by_cases h1 : i < o + 1
  · rw [dif_pos h1]
  · rw [dif_neg h1]
    split_ifs with h2
    · exact hv ⟨i, h2⟩ (by simp only; omega)
    · rfl

def NFTieGen : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    ∃ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
      IsFrameKB p e ∧ IsGaugeQQKB p e ∧ MA.IsModelLevel P (MA.DQ P) L ∧
      ∀ (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P p.l0 Y w →
      ∀ (ee : Wd.Ix (Fin w.length)) (Q : ℕ) (Lq : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq), IsSCoef p w ee Q Lq →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))) (C : ℝ),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, (u j).length = w.length ∧ ∀ a ∈ u j, a ∈ MA.hatSet P L) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          (LocLift ∨ KB.CptCoef p.T.base F) → B.JF p.T.base F ∈ FFKB p →
          ∀ (qq : Fin (Q + 1)) (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT),
            q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
            D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
            Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
              (Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) ee ρ ^ 2 *
                ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq qq) F) (TBB.bigPt P.r c)))‖ ^ 2) ≤
              C * TBB.Gp p (TBB.bigPt P.r c) ^ (-(w.length : ℤ)) *
                ∑ j, ∑ ρ' : M.Ty P, ‖MA.evQ P (MA.actA P (b j * (u j).prod) (trJKB p e (B.JF p.T.base F)) ρ') q‖ ^ 2

theorem nfTieGen_of (hK : GCore) : NFTieGen := by
  intro Cb
  obtain ⟨CcL, HL⟩ := leibniz_vector_estimate_holds Cb
  refine ⟨|CcL| + 12 + 8 * |Cb|, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p hInD
  obtain ⟨hl1, hlk, hk⟩ := p.hl
  obtain ⟨fr, hfr, hga⟩ := hK Wp Wq P p.T.base p.hP hk
  obtain ⟨Lv, hml, -⟩ := model_frame_analytic P p.hP.1 p.l0 hl1 hlk
  refine ⟨fr, Lv, hfr, hga, hml, fun Y w hw a Q Lq hSq => ?_⟩
  obtain ⟨nf, fib, o, κ, Dop, -, hIn, ho, -, hΘ⟩ := hInD w hw.1 a
  have hwo : ∀ T ∈ Dop, T.word.length ≤ o := fun T hT => by
    obtain ⟨_, _, _, _, _, -, -, h, -⟩ := hIn.2.2 T hT
    omega
  have hSm : B.SmoothCoef (B.GPos p.T.base) Dop := by rw [← nfLeib_domL_eq]; exact hIn.1
  have hCm : B.Commutes p.T.base (B.GPos p.T.base) Dop := by rw [← nfLeib_domL_eq]; exact hIn.2.1
  obtain ⟨Q', L', -, hS', hLe⟩ := HL Wp Wq P p hInD w hw.1 a
  have hloc : Loc (gM P p.l0 Lv (D.positionted w) a) := loc_nfs hml (model_nf p.hP.1 hml hl1 hlk hw.1 a).2
  choose m b u Ct hCt hb hu hpt using fun s : Fin (o + 1) => normal_form_model_point P Lv p.hP.1 hml p.l0 hl1 hlk w hw.1 a s
  obtain ⟨lam, hlam⟩ := vander' o
  let ι := Σ s : Fin (o + 1), Fin (m s)
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  set Λ : ℝ := ∑ q, ∑ s, ‖lam q s‖ ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set Cs : ℝ := ∑ s, Ct s with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun s _ => hCt s
  set Cw : ℝ := ∑ ρ' : M.Ty P, |(Top.cW P p.l0 w a ρ').re| with hCw
  have hCw0 : 0 ≤ Cw := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Fintype.card ι, fun t => b (σ t).1 (σ t).2, fun t => u (σ t).1 (σ t).2, Cw * (Λ * Cs),
    fun t => hb _ _, fun t => hu _ _, ?_⟩
  intro F A hF hcc hA hOr hJ qq ρ c q hq hl hG
  set γ := TBB.bigPt P.r c with hγ
  have hGq : TBB.Gp p γ = MA.Gq P q := gp_eq p c q hq
  have hd : ∀ a, c a ≠ 0 := fun a => (hl.1 (1, c a) (by rw [hγ]; unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  set X : ℝ := ∏ l : Fin P.r, Complex.normSq (c l.castSucc) with hXdef
  set S : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) with hSdef
  have hXS : 0 ≤ X * S := mul_nonneg (Finset.prod_nonneg fun _ _ => Complex.normSq_nonneg _) (mul_self_nonneg _)
  set Dn : ℝ := Complex.normSq ((∏ l : Fin P.r, c l.castSucc) * c (Fin.last P.r)) with hDn
  have hDn0 : 0 < Dn := Complex.normSq_pos.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun _ _ => hd _) (hd _))
  set Rs : Fin (o + 1) → ℝ := fun s => ∑ j, ∑ ρ', ‖MA.evQ P (MA.actA P (b s j * (u s j).prod)
    (trJKB p fr (B.JF p.T.base F)) ρ') q‖ ^ 2 with hRs
  have hRs0 : ∀ s, 0 ≤ Rs s := fun s => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ∑ t, ∑ ρ', ‖MA.evQ P (MA.actA P (b (σ t).1 (σ t).2 * (u (σ t).1 (σ t).2).prod)
      (trJKB p fr (B.JF p.T.base F)) ρ') q‖ ^ 2 = ∑ s, Rs s := by
    rw [Equiv.sum_comp σ (fun x : ι => ∑ ρ', ‖MA.evQ P (MA.actA P (b x.1 x.2 * (u x.1 x.2).prod)
      (trJKB p fr (B.JF p.T.base F)) ρ') q‖ ^ 2), Fintype.sum_sigma]
  rw [hsum]
  have hn1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
    have := Nat.cast_nonneg (α := ℝ) P.r
    have := Nat.cast_nonneg (α := ℝ) P.k
    linarith
  have hthr := fun s : Fin (o + 1) => thr_arith CcL Cb P.r (2 * (P.r : ℝ) + P.k + 1) w.length o s (B.opOrder Dop) A
    (Nat.cast_nonneg _) hn1 (Nat.cast_nonneg _) (by push_cast at ho; exact ho)
    (by exact_mod_cast Nat.lt_succ_iff.1 s.2) (by exact_mod_cast opOrder_le Dop hwo) hA

  set Vs : Fin (o + 1) → (Wq →L[ℂ] Wp) := fun s =>
    p.V (p.Θ.Θ w a fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (s : ℕ) : ℝ) : ℂ) • F g) γ with hVs
  have hG0 : 0 < MA.Gq P q := MA.Gq_pos P q
  have key : ∀ s : Fin (o + 1), X * S * ‖B.hsVec (Vs s)‖ ^ 2 ≤
      Ct s * MA.Gq P q ^ (2 * (s : ℕ)) * Dn⁻¹ ^ w.length * Rs s := by
    intro s
    set Fs : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
      fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ (s : ℕ) : ℝ) : ℂ) • F g with hFs
    have hJs : B.JF p.T.base Fs ∈ FFKB p := jf_Gpow p s hJ
    have hT : WeakThresholdClauses.WeakDominationThreshold P.k P.r (A - (((2 * P.r + 2) * (s : ℕ) : ℕ) : ℝ)) (B.opOrder Dop) := by
      refine jdc_thrW _ _ 0 le_rfl ?_
      unfold nDim
      push_cast
      exact (hthr s).2
    have hH : ∀ g ∈ JF.Om P.k P.r p.T.base.z p.T.base.z',
        B.opApply Dop (B.JF p.T.base Fs) g = B.JF p.T.base (p.Θ.Θ w a Fs) g := fun g hg => by
      rw [PBN.jf_congr_pos p.T.base (hΘ Fs) (by rw [nfLeib_domL_eq]; exact jdc_om_sub_gpos _ hg)]
      exact orbital_commutes_on_open_set _ _ _ _ p.T.base _ (B.opOrder Dop) Fs Dop _ subset_rfl le_rfl hT
        (inCC_Gpow_smul _ _ s hcc _) (fun p' hp' f' hf' g hg => hCm p' hp' f' hf' g (jdc_om_sub_gpos _ hg)) g hg
    have e1 := sxV p (p.Θ.Θ w a Fs) c hd hG q hq
    have hR0 : 0 ≤ Ct s * MA.Gq P q ^ (2 * (s : ℕ)) * Dn⁻¹ ^ w.length * Rs s :=
      mul_nonneg (mul_nonneg (mul_nonneg (hCt s) (by positivity)) (by positivity)) (hRs0 s)
    rw [mul_assoc X]
    refine le_of_eq_of_le e1 ?_
    by_cases h0 : B.JF p.T.base (p.Θ.Θ w a Fs) (B.gq p.T.base q.1) = 0
    · rw [h0, VLem.hsV_zero, norm_zero]; simpa using hR0
    · rw [← parseval hfr]
      have ht : ∀ ρ', rawJ P p.T.base fr (B.JF p.T.base (p.Θ.Θ w a Fs)) ρ' q = MA.evQ P (MA.actA P
          (gM P p.l0 Lv (D.positionted w) a) (trJB P p.T.base fr (B.JF p.T.base Fs)) ρ') q := by
        rcases hOr with hLL | hFc
        · exact tie_FF hLL p hfr hga hml hw.1 a hloc hSm hCm hΘ hJs hH q h0
        · obtain ⟨⟨Φ, hΦ⟩, ht⟩ := tie_cpt p hfr hga hml hw.1 a (cpt_Gpow p s hFc)
          intro ρ'
          rw [← ht, evQ_trJB p.hP hk hfr hΦ]
      simp only [ht]
      have h2 := hpt s (trJB P p.T.base fr (B.JF p.T.base F)) (trJB P p.T.base fr (B.JF p.T.base Fs)) (fun ρ' q' => by
        rw [evQ_trJB_FF p hfr hJs, evQ_trJB_FF p hfr hJ]; exact rawJ_Gpow p.hP s F ρ' q') q
      have e2 : Complex.normSq ((∏ l, q.1.1 l) * q.1.2) = Dn := by rw [hDn, hq]
      rw [e2] at h2
      exact h2

  set v : Fin (Q' + 1) → (Wq →L[ℂ] Wp) := fun j => p.V (B.opApply (L' j) F) γ with hv
  have hz : p.V (fun _ => 0) γ = 0 := by
    have := vector_multiplication_holds Wp Wq P p (fun _ => 0) F γ hl hG
    simpa using this
  have hv0 : ∀ j : Fin (Q' + 1), o < j → v j = 0 := fun j hj => by
    rw [← hz]
    exact PBE.vecV_congrGPos _ _ _ _ fun g hg =>
      scoef_zero p hS' hwo hΘ hF (by rw [nfLeib_domL_eq]; exact hg) j hj
  have hVv : ∀ s : Fin (o + 1), ∑ j : Fin (o + 1), (((s : ℕ) : ℂ) ^ (j : ℕ)) •
      (if h : (j : ℕ) < Q' + 1 then v ⟨j, h⟩ else 0) = ((MA.Gq P q ^ (s : ℕ) : ℝ) : ℂ)⁻¹ • Vs s := by
    intro s
    have h1 := hLe (fun x => x ^ (s : ℕ)) (contDiff_id.pow _) F A hF hcc (hthr s).1 γ hl hG
    have hne : ((MA.Gq P q ^ (s : ℕ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hG0 _).ne'
    rw [← sum_trunc _ v hv0, eq_inv_smul_iff₀ hne, Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h1.symm
    rw [nf_xD_iter_pow, hGq, smul_smul]
    congr 1
    push_cast; ring
  have hbd : ‖B.hsVec (p.V (B.opApply (Lq qq) F) γ)‖ ^ 2 ≤
      Λ * ∑ s : Fin (o + 1), (MA.Gq P q ^ (2 * (s : ℕ)))⁻¹ * ‖B.hsVec (Vs s)‖ ^ 2 := by
    have hS0 : 0 ≤ ∑ s : Fin (o + 1), (MA.Gq P q ^ (2 * (s : ℕ)))⁻¹ * ‖B.hsVec (Vs s)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    by_cases hqo : (qq : ℕ) < o + 1
    · have e1 : p.V (B.opApply (Lq qq) F) γ = if h : (qq : ℕ) < Q' + 1 then v ⟨qq, h⟩ else 0 := by
        split_ifs with h
        · exact PBE.vecV_congrGPos _ _ _ _ fun g hg => by
            rw [nf_scoef_unique p w a hSq hS' F hF g (by rw [nfLeib_domL_eq]; exact hg) qq, dif_pos (by omega)]
        · rw [← hz]
          exact PBE.vecV_congrGPos _ _ _ _ fun g hg => by
            rw [nf_scoef_unique p w a hSq hS' F hF g (by rw [nfLeib_domL_eq]; exact hg) qq, dif_neg (by omega)]
      have e2 := hlam _ (fun j : Fin (o + 1) => if h : (j : ℕ) < Q' + 1 then v ⟨j, h⟩ else 0) ⟨qq, hqo⟩
      simp only [hVv] at e2
      rw [e1, e2, tc_hsVec_sum]
      simp only [tc_hsVec_smul]
      refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2) ?_
      simp only [norm_smul]
      refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) (mul_le_mul ?_ (le_of_eq ?_) ?_ hΛ0)
      · exact Finset.single_le_sum (f := fun q => ∑ s, ‖lam q s‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      · refine Finset.sum_congr rfl fun s _ => ?_
        rw [mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hG0.le _), inv_pow, ← pow_mul,
          mul_comm (s : ℕ) 2]
      · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    · have e1 : p.V (B.opApply (Lq qq) F) γ = 0 := by
        rw [← hz]
        exact PBE.vecV_congrGPos _ _ _ _ fun g hg =>
          scoef_zero p hSq hwo hΘ hF (by rw [nfLeib_domL_eq]; exact hg) qq (by omega)
      rw [e1, VLem.hsV_zero, norm_zero]
      simpa using mul_nonneg hΛ0 hS0
  have h3 : X * S * ‖B.hsVec (p.V (B.opApply (Lq qq) F) γ)‖ ^ 2 ≤ Λ * Cs * Dn⁻¹ ^ w.length * ∑ s, Rs s := by
    refine le_trans (mul_le_mul_of_nonneg_left hbd hXS) ?_
    rw [mul_left_comm, mul_assoc Λ, mul_assoc Λ]
    refine mul_le_mul_of_nonneg_left ?_ hΛ0
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hp : 0 < MA.Gq P q ^ (2 * (s : ℕ)) := pow_pos hG0 _
    rw [mul_left_comm, inv_mul_le_iff₀ hp]
    refine le_trans (key s) ?_
    have : Ct s ≤ Cs := Finset.single_le_sum (f := Ct) (fun s _ => hCt s) (Finset.mem_univ s)
    have h4 : 0 ≤ MA.Gq P q ^ (2 * (s : ℕ)) * Dn⁻¹ ^ w.length * Rs s :=
      mul_nonneg (by positivity) (hRs0 s)
    nlinarith [mul_le_mul_of_nonneg_right this h4]
  have h5 := dH_sq_le p w a ρ c hG
  have h6 := hsVec_proj_le (p.TP.E ρ) (p.TP.idem ρ) (p.TP.selfAdj ρ) (p.V (B.opApply (Lq qq) F) γ)
  have hW0 : 0 ≤ Cw * (Dn / TBB.Gp p γ) ^ w.length := by positivity
  calc S * X * (Top.dH P p.l0 (TBB.TTp p) w γ a ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq qq) F) γ))‖ ^ 2)
      ≤ S * X * (Cw * (Dn / TBB.Gp p γ) ^ w.length * ‖B.hsVec (p.V (B.opApply (Lq qq) F) γ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h5 h6 (sq_nonneg _) hW0) (by rw [mul_comm]; exact hXS)
    _ = Cw * (Dn / TBB.Gp p γ) ^ w.length * (X * S * ‖B.hsVec (p.V (B.opApply (Lq qq) F) γ)‖ ^ 2) := by ring
    _ ≤ Cw * (Dn / TBB.Gp p γ) ^ w.length * (Λ * Cs * Dn⁻¹ ^ w.length * ∑ s, Rs s) :=
        mul_le_mul_of_nonneg_left h3 hW0
    _ = _ := by
        rw [zpow_neg, zpow_natCast, div_pow, inv_pow]
        have := (pow_pos hDn0 w.length).ne'
        have := (pow_pos hG w.length).ne'
        field_simp

end

end Formalism.FourierDecayAlt.P.NormalFormRelations
