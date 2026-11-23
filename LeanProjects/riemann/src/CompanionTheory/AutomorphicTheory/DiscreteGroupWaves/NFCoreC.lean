import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFDomS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeibMain

namespace CompanionTheory.NFCpt

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Filter Topology MeasureTheory

noncomputable section

def NFTieHatC : Prop :=
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
          KB.CptCoef p.T.base F → B.JF p.T.base F ∈ FFKB p →
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

def NFCoreNC : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → ∀ (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P p.l0 Y w →
    ∀ (e : Wd.Ix (Fin w.length)) (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq), IsSCoef p w e Q L →
    ∀ p₀ N : ℕ, w.length ≤ N → N ≤ 2 * p₀ →
      ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (Mb : ℝ), 0 ≤ Mb ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
        ∀ (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
            A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
          KB.CptCoef p.T.base f → B.JF p.T.base f ∈ FFKB p →
          ∀ (q : Fin (Q + 1)) (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ), D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
            0 < TBB.Gp p (TBB.bigPt P.r c) →
            Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) e ρ ^ 2 *
                ‖B.hsVec ((p.TP.E ρ).comp
                  (p.V (B.opApply (L q) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) (TBB.bigPt P.r c)))‖ ^ 2 ≤
              Mb * TBB.Gp p (TBB.bigPt P.r c) ^ (2 * p₀ - N) *
                ∑ t, ‖B.hsVec (p.V (B.opApply (Th t) f) (TBB.bigPt P.r c))‖ ^ 2

theorem nFCoreNC_of_cut (hL : NFLeibV) (hT : NFTieHatC) (hH : NFHatProdKBS) (hN : NFTrNormKB) (hM : NFOpOKMulG) :
    NFCoreNC := by
  intro Cb
  obtain ⟨CcL, HL⟩ := hL Cb
  obtain ⟨CcT, HT⟩ := hT Cb
  obtain ⟨IsFirstChernFamily, CcH, HH⟩ := hH
  obtain ⟨C1M, HM⟩ := hM IsFirstChernFamily
  set Mx := max (max CcL CcT) (max CcH 0) with hMx
  refine ⟨Mx, max IsFirstChernFamily C1M, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p hΘ Y w hw e Q L hS p₀ N hwN hNp
  have thr : ∀ C : ℝ, C ≤ Mx → ∀ n : ℕ, n ≤ N → ∀ A : ℝ,
      Mx * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      C * ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC n hn A hA
    have hM0 : 0 ≤ Mx := le_trans (le_max_right _ _) (le_max_right _ _)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have hXN : ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      gcongr
    have e : ∀ (x : ℝ) (m : ℕ), x * ((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x m => by ring
    rw [e] at hA ⊢
    exact le_trans (mul_le_mul_of_nonneg_right hC hX) (le_trans (mul_le_mul_of_nonneg_left hXN hM0) hA)
  obtain ⟨Q', L', -, hS', hLe⟩ := HL Wp Wq P p hΘ w hw.1 e
  obtain ⟨fr, Lv, hfr, hgau, hml, hTie⟩ := HT Wp Wq P p hΘ
  obtain ⟨m, b, u, Ct, hb, hu, htie⟩ := hTie Y w hw e Q' L' hS'
  choose m' b' Th hb' hok hprod using fun i : Fin m =>
    HH Wp Wq P p fr Lv hfr hgau hml N (u i) (by rw [(hu i).1]; exact hwN) (hu i).2
  have hTTe : P.TT = Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' := by
    unfold M.Par.TT
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  have hTTpos : 0 < P.TT := by rw [hTTe]; exact mul_pos p.T.base.T_pos p.T.base.T'_pos
  choose Cbd hCbd using fun (i : Fin m) (k : Fin (m' i)) =>
    pointwise_bound_normal_form_holds P Lv hTTpos hml (b i * b' i k) (Submonoid.mul_mem _ (hb i) (hb' i k))
  obtain ⟨Cn, hCn⟩ := hN Wp Wq P p fr hfr
  choose Th2 hok2 hTh2 using fun (i : Fin m) (k : Fin (m' i)) => HM Wp Wq P p N (Th i k) (hok i k)
  let ι := Σ i : Fin m, Fin (m' i) × Bool
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let ThF : ι → B.DiffOp P.k P.r Wp Wq := fun x => if x.2.2 then Th2 x.1 x.2.1 else Th x.1 x.2.1
  set K : ℝ := ∑ i : Fin m, ∑ k : Fin (m' i), (m' i : ℝ) * |Cbd i k| * |Cn| * |Ct| with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity
  set cc : Fin (Q' + 1) → Fin (Q' + 1) → ℝ := fun qq j => ((Nat.choose j qq * p₀ ^ ((j : ℕ) - qq) : ℕ) : ℝ) with hcc
  set Cs : ℝ := ∑ qq : Fin (Q' + 1), ((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq j ^ 2 with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun qq _ => by positivity
  refine ⟨Fintype.card ι, fun t => ThF (σ t), Cs * K, mul_nonneg hCs0 hK0, fun t => ?_, ?_⟩
  · show NFOpOK (max IsFirstChernFamily C1M) p N (ThF (σ t))
    simp only [ThF]
    split_ifs
    · exact nfOpOK_mono (hok2 _ _) (le_max_right _ _)
    · exact nfOpOK_mono (hok _ _) (le_max_left _ _)
  intro f A₀ hf hcc0 hthr hCp hJ qq ρ c hl hG
  set γ := TBB.bigPt P.r c with hγ
  set G := TBB.Gp p γ with hGdef
  have hG0 : 0 ≤ G := hG.le
  have hd : ∀ a, c a ≠ 0 := fun a => (hl.1 (1, c a) (by rw [hγ]; unfold TBB.bigPt; exact List.mem_ofFn.2 ⟨a, rfl⟩)).2
  have hζ : P.TT < Complex.normSq (c (Fin.last P.r)) := by
    rw [hTTe]; exact Formalism.FourierDecayAlt.P.PBM.zeta_big _ c hG
  let q : MA.Qp P.r P.TT := ⟨((fun l => c l.castSucc), c (Fin.last P.r)), fun l => hd _, hζ⟩
  set X : ℝ := ∏ l : Fin P.r, Complex.normSq (c l.castSucc) with hXdef
  have hX : 0 < X := Finset.prod_pos fun l _ => Complex.normSq_pos.2 (hd _)
  have hζ' : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' ≤ Complex.normSq (c (Fin.last P.r)) := by
    rw [← hTTe]; exact hζ.le
  have hn : 0 < TBB.nPt P.k P.r (TBB.TTp p) γ := by
    have e1 := nPt_bigPt P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') c hζ'
    show 0 < TBB.nPt P.k P.r (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') (TBB.bigPt P.r c)
    rw [e1]
    unfold bcWeight
    rw [if_pos hζ']
    refine mul_pos (Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hd _)) _) (pow_pos ?_ _)
    rw [← hTTe]; linarith
  set S : ℝ := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) with hSdef
  have hSpos : 0 < S := mul_pos (Real.sqrt_pos.2 hn) (Real.sqrt_pos.2 hn)
  set Vk : ∀ i : Fin m, Fin (m' i) → ℝ := fun i k => ‖B.hsVec (p.V (B.opApply (Th i k) f) γ)‖ ^ 2 with hVk
  set W : ℝ := ∑ i, ∑ k, Vk i k with hW
  have hVk0 : ∀ i k, 0 ≤ Vk i k := fun i k => sq_nonneg _
  have hVkW : ∀ i k, Vk i k ≤ W := fun i k =>
    le_trans (Finset.single_le_sum (f := fun k => Vk i k) (fun k _ => hVk0 i k) (Finset.mem_univ k))
      (Finset.single_le_sum (f := fun i => ∑ k, Vk i k) (fun i _ => Finset.sum_nonneg fun k _ => hVk0 i k)
        (Finset.mem_univ i))
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => hVk0 i k
  have hA0 : A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ A₀ := sub_le_self _ (Nat.cast_nonneg _)
  have hthrT := thr CcT (le_trans (le_max_right _ _) (le_max_left _ _)) w.length hwN A₀ (le_trans hthr hA0)
  have hthrH := thr CcH (le_trans (le_max_left _ _) (le_max_right _ _)) N le_rfl A₀ (le_trans hthr hA0)
  have hthrL := thr CcL (le_trans (le_max_left _ _) (le_max_left _ _)) w.length hwN _ hthr

  have stepAB : ∀ j : Fin (Q' + 1), Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (L' j) f) γ))‖ ^ 2 ≤ G ^ (-(w.length : ℤ)) * (K * W) := by
    intro j
    have h1 := htie f A₀ hf hcc0 hthrT hCp hJ j ρ c q rfl hl hG
    have h2 : ∀ i, ∑ ρ', ‖MA.evQ P (MA.actA P (b i * (u i).prod) (trJKB p fr (B.JF p.T.base f)) ρ') q‖ ^ 2 ≤
        ∑ k, (m' i : ℝ) * |Cbd i k| * |Cn| * (X * (S * Vk i k)) := by
      intro i
      rw [Formalism.FourierDecayAlt.P.MAx3.F.actA_mul, hprod i f A₀ hf hcc0 hthrH hJ, nf_actA_fsum]
      simp only [← Formalism.FourierDecayAlt.P.MAx3.F.actA_mul]
      have hj : ∀ k ρ', ‖MA.evQ P (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)) ρ') q‖ ^ 2 ≥ 0 :=
        fun _ _ => sq_nonneg _
      calc ∑ ρ', ‖MA.evQ P ((∑ k, MA.actA P (b i * b' i k) (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)))) ρ') q‖ ^ 2
          ≤ ∑ ρ', (m' i : ℝ) * ∑ k, ‖MA.evQ P (MA.actA P (b i * b' i k)
              (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f))) ρ') q‖ ^ 2 := by
            refine Finset.sum_le_sum fun ρ' _ => ?_
            rw [Finset.sum_apply, Formalism.FourierDecayAlt.P.MAx2.Jet.evQ_sum]
            have := nf_norm_sum_sq (Finset.univ : Finset (Fin (m' i))) fun k =>
              MA.evQ P (MA.actA P (b i * b' i k) (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f))) ρ') q
            rwa [Finset.card_univ, Fintype.card_fin] at this
        _ = (m' i : ℝ) * ∑ k, ∑ ρ', ‖MA.evQ P (MA.actA P (b i * b' i k)
              (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f))) ρ') q‖ ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ (m' i : ℝ) * ∑ k, |Cbd i k| * (|Cn| * (X * (S * Vk i k))) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (Nat.cast_nonneg _)
            have hb1 := hCbd i k (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f))) q
            have hn1 := hCn (B.opApply (Th i k) f) c q rfl hl hG
            rw [TBBx2.Tri.Ew_top p _ hl] at hn1
            have hs0 : 0 ≤ ∑ ρ', ‖MA.evQ P (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)) ρ') q‖ ^ 2 :=
              Finset.sum_nonneg fun _ _ => sq_nonneg _
            have hE0 : 0 ≤ X * (S * Vk i k) := mul_nonneg hX.le (mul_nonneg hSpos.le (hVk0 i k))
            have hn2 : ∑ ρ', ‖MA.evQ P (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)) ρ') q‖ ^ 2 ≤
                |Cn| * (X * (S * Vk i k)) := by
              refine le_trans hn1 (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right (le_abs_self Cn) hE0))
              simp only [hVk, hSdef, hXdef, hγ]; ring
            calc _ ≤ Cbd i k * ∑ ρ', ‖MA.evQ P (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)) ρ') q‖ ^ 2 := hb1
              _ ≤ |Cbd i k| * ∑ ρ', ‖MA.evQ P (trJKB p fr (B.JF p.T.base (B.opApply (Th i k) f)) ρ') q‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right (le_abs_self _) hs0
              _ ≤ |Cbd i k| * (|Cn| * (X * (S * Vk i k))) := mul_le_mul_of_nonneg_left hn2 (abs_nonneg _)
        _ = ∑ k, (m' i : ℝ) * |Cbd i k| * |Cn| * (X * (S * Vk i k)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have hGz : 0 ≤ G ^ (-(w.length : ℤ)) := zpow_nonneg hG0 _
    have h3 : S * X * (Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (L' j) f) γ))‖ ^ 2) ≤
        S * X * (G ^ (-(w.length : ℤ)) * (K * W)) := by
      refine le_trans h1 ?_
      have hsum0 : 0 ≤ ∑ i, ∑ ρ', ‖MA.evQ P (MA.actA P (b i * (u i).prod) (trJKB p fr (B.JF p.T.base f)) ρ') q‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc Ct * G ^ (-(w.length : ℤ)) * ∑ i, ∑ ρ', ‖MA.evQ P (MA.actA P (b i * (u i).prod) (trJKB p fr (B.JF p.T.base f)) ρ') q‖ ^ 2
          ≤ |Ct| * G ^ (-(w.length : ℤ)) * ∑ i, ∑ k, (m' i : ℝ) * |Cbd i k| * |Cn| * (X * (S * Vk i k)) := by
            refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ct) hGz) hsum0) ?_
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (mul_nonneg (abs_nonneg _) hGz)
        _ = S * X * (G ^ (-(w.length : ℤ)) * ∑ i, ∑ k, (m' i : ℝ) * |Cbd i k| * |Cn| * |Ct| * Vk i k) := by
            simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        _ ≤ S * X * (G ^ (-(w.length : ℤ)) * (K * W)) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hGz) (mul_nonneg hSpos.le hX.le)
            rw [hK, Finset.sum_mul]
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hVkW i k) (by positivity)
    exact le_of_mul_le_mul_left h3 (mul_pos hSpos hX)

  have hV2 : ∀ i k, p.V (B.opApply (Th2 i k) f) γ = ((G ^ N : ℝ) : ℂ) • p.V (B.opApply (Th i k) f) γ := by
    intro i k
    have e1 : B.opApply (Th2 i k) f =
        fun g => (((fun x : ℝ => x ^ N) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • B.opApply (Th i k) f g :=
      funext fun g => hTh2 i k f g
    rw [e1]
    exact vector_multiplication_holds Wp Wq P p (fun x : ℝ => x ^ N) _ γ hl hG
  have hsumT : ∑ t, ‖B.hsVec (p.V (B.opApply (ThF (σ t)) f) γ)‖ ^ 2 = (1 + G ^ (2 * N)) * W := by
    rw [Equiv.sum_comp σ (fun x : ι => ‖B.hsVec (p.V (B.opApply (ThF x) f) γ)‖ ^ 2), Fintype.sum_sigma, hW,
      add_mul, one_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_bool]
    simp only [ThF, if_true, Bool.false_eq_true, if_false, hV2, CutSE.hsVec_smul', norm_smul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hVk]
    rw [← pow_mul, mul_comm N 2]
    ring

  have hF' : B.CkOn ⊤ (B.GV P.k P.r) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) := by
    rw [fpm_id]; exact ckOn_Gpow_smul p.T.base.z p.T.base.z' p₀ hf
  have hRHS0 : 0 ≤ Cs * K * G ^ (2 * p₀ - N) * ∑ t, ‖B.hsVec (p.V (B.opApply (ThF (σ t)) f) γ)‖ ^ 2 := by
    have := pow_nonneg hG0 (2 * p₀ - N)
    have : 0 ≤ ∑ t, ‖B.hsVec (p.V (B.opApply (ThF (σ t)) f) γ)‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hcong : ∀ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      (∀ g ∈ B.GPos p.T.base, B.opApply (L qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) g = H₂ g) →
      p.V (B.opApply (L qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ = p.V H₂ γ := by
    intro H₂ h
    exact Formalism.FourierDecayAlt.P.PBE.vecV_congrGPos _ _ _ _ h
  have hdom : ∀ g ∈ B.GPos p.T.base, g ∈ C6.domL p.T.base ∅ := fun g hg =>
    ⟨hg.1, hg.2, fun l hl => absurd hl (Finset.notMem_empty l)⟩
  by_cases hqQ : (qq : ℕ) ≤ Q'
  swap
  · have h0 : p.V (B.opApply (L qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ = 0 := by
      rw [hcong (fun g => (((fun _ : ℝ => (0 : ℝ)) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • f g)]
      · rw [vector_multiplication_holds Wp Wq P p (fun _ : ℝ => (0 : ℝ)) f γ hl hG]; simp
      · intro g hg
        rw [nf_scoef_unique p w e hS hS' _ hF' g (hdom g hg) qq, dif_neg hqQ]
        simp
    have hz : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by unfold B.hsVec; ext i; simp
    rw [h0, ContinuousLinearMap.comp_zero, hz, norm_zero]
    simpa using hRHS0
  set qq' : Fin (Q' + 1) := ⟨qq, by omega⟩ with hqq'
  have hV1 : p.V (B.opApply (L qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ =
      ((G ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1), ((cc qq' j : ℝ) : ℂ) • p.V (B.opApply (L' j) f) γ := by
    rw [hcong (B.opApply (L' qq') (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀))]
    · rw [nf_vExtract p w e L' CcL hLe f A₀ p₀ hf hcc0 hthrL γ hl hG qq']
      congr 1
    · intro g hg
      rw [nf_scoef_unique p w e hS hS' _ hF' g (hdom g hg) qq, dif_pos hqQ]

  let Λ : (Wq →L[ℂ] Wp) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
    { toFun := fun Y => B.hsVec ((p.TP.E ρ).comp Y)
      map_add' := fun Y₁ Y₂ => by rw [ContinuousLinearMap.comp_add, CutSE.hsVec_add']
      map_smul' := fun a Y => by rw [ContinuousLinearMap.comp_smul, CutSE.hsVec_smul']; rfl }
  have hΛ : ∀ Y, Λ Y = B.hsVec ((p.TP.E ρ).comp Y) := fun Y => rfl
  set dd : ℝ := Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 with hdd
  have hdd0 : 0 ≤ dd := sq_nonneg _
  set Y : Fin (Q' + 1) → (Wq →L[ℂ] Wp) := fun j => p.V (B.opApply (L' j) f) γ with hY
  have hnorm : ‖B.hsVec ((p.TP.E ρ).comp (((G ^ p₀ : ℝ) : ℂ) • ∑ j, ((cc qq' j : ℝ) : ℂ) • Y j))‖ ≤
      G ^ p₀ * ∑ j, cc qq' j * ‖Λ (Y j)‖ := by
    rw [← hΛ, map_smul, map_sum, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hG0 _)]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)))
      (pow_nonneg hG0 _)
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  have hcs : (∑ j, cc qq' j * ‖Λ (Y j)‖) ^ 2 ≤ ((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq' j ^ 2 * ‖Λ (Y j)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (Q' + 1)))) (f := fun j => cc qq' j * ‖Λ (Y j)‖)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine le_trans this (le_of_eq ?_)
    congr 1; exact Finset.sum_congr rfl fun j _ => by ring
  have hCsq : ((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq' j ^ 2 ≤ Cs :=
    Finset.single_le_sum (f := fun qq : Fin (Q' + 1) => ((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq j ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ qq')
  have hGw : G ^ (2 * p₀) * G ^ (-(w.length : ℤ)) ≤ G ^ (2 * p₀ - N) * (1 + G ^ (2 * N)) := by
    have e1 : G ^ (2 * p₀) * G ^ (-(w.length : ℤ)) = G ^ (2 * p₀ - N) * G ^ (N - w.length) := by
      rw [zpow_neg, zpow_natCast, ← pow_add, show 2 * p₀ - N + (N - w.length) = 2 * p₀ - w.length by omega]
      rw [← pow_sub_mul_pow G (show w.length ≤ 2 * p₀ by omega)]
      rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hG.ne'), mul_one]
    rw [e1]
    exact mul_le_mul_of_nonneg_left (nf_pow_le G hG0 (Nat.sub_le N w.length)) (pow_nonneg hG0 _)
  rw [hV1, hsumT]
  calc dd * ‖B.hsVec ((p.TP.E ρ).comp (((G ^ p₀ : ℝ) : ℂ) • ∑ j, ((cc qq' j : ℝ) : ℂ) • Y j))‖ ^ 2
      ≤ dd * (G ^ p₀ * ∑ j, cc qq' j * ‖Λ (Y j)‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hdd0
    _ = G ^ (2 * p₀) * (dd * (∑ j, cc qq' j * ‖Λ (Y j)‖) ^ 2) := by rw [mul_pow, ← pow_mul, mul_comm p₀ 2]; ring
    _ ≤ G ^ (2 * p₀) * (((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq' j ^ 2 * (dd * ‖Λ (Y j)‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hG0 _)
        refine le_trans (mul_le_mul_of_nonneg_left hcs hdd0) (le_of_eq ?_)
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ G ^ (2 * p₀) * (((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq' j ^ 2 * (G ^ (-(w.length : ℤ)) * (K * W))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by positivity))
          (pow_nonneg hG0 _)
        exact mul_le_mul_of_nonneg_left (stepAB j) (sq_nonneg _)
    _ = (G ^ (2 * p₀) * G ^ (-(w.length : ℤ))) * ((((Q' + 1 : ℕ) : ℝ) * ∑ j, cc qq' j ^ 2) * (K * W)) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (G ^ (2 * p₀ - N) * (1 + G ^ (2 * N))) * (Cs * (K * W)) := by
        refine mul_le_mul hGw (mul_le_mul_of_nonneg_right hCsq (mul_nonneg hK0 hW0)) ?_ ?_
        · exact mul_nonneg (by positivity) (mul_nonneg hK0 hW0)
        · exact mul_nonneg (pow_nonneg hG0 _) (by positivity)
    _ = Cs * K * G ^ (2 * p₀ - N) * ((1 + G ^ (2 * N)) * W) := by ring

def NFDomPtwC : Prop :=
  ∀ Cb : ℝ, ∃ Cc C₁ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ) (w : List C.Letter), TBB.AdmW P p.l0 Y w → w.length ≤ N →
      ∃ (m : ℕ) (Th : Fin m → B.DiffOp P.k P.r Wp Wq) (Mb : ℝ), 0 ≤ Mb ∧ (∀ t, NFOpOK C₁ p N (Th t)) ∧
        ∀ (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ), NFHyp Cb Cc p f A₀ p₀ χ N → KB.CptCoef p.T.base f →
        B.JF p.T.base f ∈ FFKB p →
        ∀ ε : ℝ, 0 < ε → ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) →
          0 < TBB.Gp p (TBB.bigPt P.r c) →
          ‖topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w c‖ ≤
            Mb * ∑ t, ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
              TBB.Ew p (fun _ => 1) (B.opApply (Th t) f) (P.r + 1) [] (TBB.bigPt P.r c)

theorem nfDomPtwC_of_cut (hU : NFUnfoldTop) (hV : NFVMul) (hC : NFCutSup) (hL : NFLeibV) (hN : NFCoreNC)
    (hE : NFEmptyOps) : NFDomPtwC := by
  intro Cb
  obtain ⟨CcL, HL⟩ := hL Cb
  obtain ⟨CcN, C1N, HN⟩ := hN Cb
  obtain ⟨C1E, HE⟩ := hE
  refine ⟨max (max CcL CcN) 0, max C1N C1E, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p p₀ χ Y N w hw hwN
  by_cases hpre : C6.IsCut0 χ ∧ KB.InDDplus2 P p.l0 p.T.base Cb p.Θ ∧ N ≤ 2 * p₀
  swap
  · refine ⟨0, Fin.elim0, 0, le_rfl, fun t => t.elim0, ?_⟩
    intro f A₀ hH
    exact absurd ⟨hH.1, hH.2.1, hH.2.2.2.2.2⟩ hpre
  obtain ⟨hχ, hΘ, hNp⟩ := hpre
  set Mx := max (max CcL CcN) 0 with hMx
  have thr : ∀ C : ℝ, C ≤ Mx → ∀ n : ℕ, n ≤ N → ∀ A : ℝ,
      Mx * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      C * ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC n hn A hA
    have hM0 : 0 ≤ Mx := le_max_right _ _
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      positivity
    have hXN : ((P.r : ℝ) + 1) ^ 4 * ((n : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
      gcongr
    have e : ∀ (x : ℝ) (m : ℕ), x * ((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
        x * (((P.r : ℝ) + 1) ^ 4 * ((m : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
      fun x m => by ring
    rw [e] at hA ⊢
    exact le_trans (mul_le_mul_of_nonneg_right hC hX) (le_trans (mul_le_mul_of_nonneg_left hXN hM0) hA)
  by_cases hw0 : w = []
  · subst hw0
    obtain ⟨Th₀, Th₁, h0, h1, hap⟩ := HE Wp Wq P p N
    obtain ⟨K, hK⟩ := hC χ hχ 0
    refine ⟨2, ![Th₀, Th₁], K ^ 2, sq_nonneg _, Fin.forall_fin_two.mpr
      ⟨nfOpOK_mono h0 (le_max_right _ _), nfOpOK_mono h1 (le_max_right _ _)⟩, ?_⟩
    intro f A₀ hH hCp hJ ε hε c hl hG
    have hK' : |χ (TBB.Gp p (TBB.bigPt P.r c) / ε)| ≤ K := by simpa using hK ε hε _ hG
    exact nf_empty_bound hV p f p₀ N hNp χ K Th₀ Th₁ hap ε c hl hG hK'
  have hcut : KB.CutWord P p.l0 w := hw.1
  choose Q Lq hLs hLS hLe using fun e : Wd.Ix (Fin w.length) => HL Wp Wq P p hΘ w hcut e
  choose m Th Mb hMb hok hb using
    fun e : Wd.Ix (Fin w.length) => HN Wp Wq P p hΘ Y w hw e (Q e) (Lq e) (hLS e) p₀ N hwN hNp
  choose K hK using fun q : ℕ => hC χ hχ q
  set Ke : Wd.Ix (Fin w.length) → ℝ := fun e => ∑ q : Fin (Q e + 1), |K q| with hKe
  set nT : ℝ := ((Finset.univ : Finset (M.Ty P)).card : ℝ) with hnT
  set Cst : Wd.Ix (Fin w.length) → ℝ := fun e => nT * ((((Q e + 1 : ℕ) : ℝ)) ^ 2 * Ke e ^ 2 * Mb e) with hCst
  have hCst0 : ∀ e, 0 ≤ Cst e := fun e => by
    simp only [hCst]; have := hMb e; positivity
  let ι := Σ e : Wd.Ix (Fin w.length), Fin (m e)
  let σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => Th (σ i).1 (σ i).2, ∑ e, Cst e, Finset.sum_nonneg fun e _ => hCst0 e,
    fun i => nfOpOK_mono (hok _ _) (le_max_left _ _), ?_⟩
  intro f A₀ hH hCp hJ ε hε c hl hG
  set γ := TBB.bigPt P.r c with hγ
  set G := TBB.Gp p γ with hGdef
  set F := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hFdef
  have hF : B.CkOn ⊤ (B.GV P.k P.r) F := by
    rw [hFdef, fpm_id]; exact ckOn_Gpow_smul p.T.base.z p.T.base.z' p₀ hH.2.2.1
  have hFcc := inCC_fpm_id p p₀ hH.2.2.2.1
  have hthrL := thr CcL (le_trans (le_max_left _ _) (le_max_left _ _)) w.length hwN _ hH.2.2.2.2.1
  have hthrN := thr CcN (le_trans (le_max_right _ _) (le_max_left _ _)) N le_rfl _ hH.2.2.2.2.1
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : ℝ => χ (y / ε)) := hχ.1.comp (contDiff_id.div_const ε)
  set S := Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) * Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) γ) with hS
  have hS0 : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set B' : Wd.Ix (Fin w.length) → ℝ := fun e => ∑ t, ‖B.hsVec (p.V (B.opApply (Th e t) f) γ)‖ ^ 2 with hB'
  have hB'0 : ∀ e, 0 ≤ B' e := fun e => Finset.sum_nonneg fun t _ => sq_nonneg _
  have hG0 : 0 ≤ G := hG.le
  have key : ∀ e ρ, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 ≤
      (((Q e + 1 : ℕ) : ℝ)) ^ 2 * Ke e ^ 2 * Mb e * (G ^ (2 * p₀ - N) * B' e) := by
    intro e ρ
    have hexp := hLe e (fun y => χ (y / ε)) hφ F _ hF hFcc hthrL γ hl hG
    have hc : D.cutF p.T.base χ F ε =
        fun g => (((fun y => χ (y / ε)) (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g := rfl
    rw [hc, hexp]
    have ha : ∀ q : Fin (Q e + 1), |(xD^[(q : ℕ)] (fun y => χ (y / ε))) G| ≤ Ke e := by
      intro q
      refine le_trans (hK q ε hε G hG) ?_
      refine le_trans (le_abs_self _) ?_
      exact Finset.single_le_sum (f := fun q : Fin (Q e + 1) => |K q|) (fun _ _ => abs_nonneg _) (Finset.mem_univ q)
    refine le_trans (nf_block (p.TP.E ρ) (fun q : Fin (Q e + 1) => (xD^[(q : ℕ)] (fun y => χ (y / ε))) G) (Ke e) ha
      (fun q => p.V (B.opApply (Lq e q) F) γ) _) ?_
    have hq : ∀ q : Fin (Q e + 1), Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq e q) F) γ))‖ ^ 2 ≤ Mb e * G ^ (2 * p₀ - N) * B' e :=
      fun q => hb e f A₀ hH.2.2.1 hH.2.2.2.1 hthrN hCp hJ q ρ c hl hG
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ (Finset.univ : Finset (Fin (Q e + 1)))) => hq q
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hK2 : 0 ≤ ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 := by positivity
    calc ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 * ∑ q : Fin (Q e + 1), Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
          ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq e q) F) γ))‖ ^ 2
        ≤ ((Q e + 1 : ℕ) : ℝ) * Ke e ^ 2 * (((Q e + 1 : ℕ) : ℝ) * (Mb e * G ^ (2 * p₀ - N) * B' e)) :=
          mul_le_mul_of_nonneg_left hsum hK2
      _ = _ := by ring
  rw [hU Wp Wq P p _ w c hw0 hl hG]
  have hin : ∀ e, 0 ≤ ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 :=
    fun e => Finset.sum_nonneg fun ρ _ => by positivity
  rw [Real.norm_of_nonneg (mul_nonneg hS0 (Finset.sum_nonneg fun e _ => hin e))]
  have hE : ∀ e t, TBB.Ew p (fun _ => 1) (B.opApply (Th e t) f) (P.r + 1) [] γ =
      S * ‖B.hsVec (p.V (B.opApply (Th e t) f) γ)‖ ^ 2 := fun e t => TBBx2.Tri.Ew_top p _ hl
  have hR : ∑ i : Fin (Fintype.card ι), ‖G‖ ^ (2 * p₀ - N) *
        TBB.Ew p (fun _ => 1) (B.opApply (Th (σ i).1 (σ i).2) f) (P.r + 1) [] γ =
      ∑ e, G ^ (2 * p₀ - N) * (S * B' e) := by
    rw [Equiv.sum_comp σ (fun x : ι => ‖G‖ ^ (2 * p₀ - N) *
      TBB.Ew p (fun _ => 1) (B.opApply (Th x.1 x.2) f) (P.r + 1) [] γ), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hE, Real.norm_of_nonneg hG0, hB', Finset.mul_sum]
  rw [hR]
  have hblock : ∀ e, ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
      ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2 ≤
      Cst e * (G ^ (2 * p₀ - N) * B' e) := by
    intro e
    refine le_trans (Finset.sum_le_sum fun ρ _ => key e ρ) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    simp only [hCst, hnT]
    exact le_of_eq (by ring)
  have hGB : ∀ e, 0 ≤ G ^ (2 * p₀ - N) * (S * B' e) := fun e => by have := hB'0 e; positivity
  calc S * ∑ e, ∑ ρ : M.Ty P, Top.dH P p.l0 (TBB.TTp p) w γ e ρ ^ 2 *
        ‖B.hsVec ((p.TP.E ρ).comp (p.V (p.Θ.Θ w e (D.cutF p.T.base χ F ε)) γ))‖ ^ 2
      ≤ S * ∑ e, Cst e * (G ^ (2 * p₀ - N) * B' e) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e _ => hblock e) hS0
    _ = ∑ e, Cst e * (G ^ (2 * p₀ - N) * (S * B' e)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
    _ ≤ ∑ e, (∑ e', Cst e') * (G ^ (2 * p₀ - N) * (S * B' e)) :=
        Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun e' _ => hCst0 e') (Finset.mem_univ e)) (hGB e)
    _ = (∑ e, Cst e) * ∑ e, G ^ (2 * p₀ - N) * (S * B' e) := by rw [Finset.mul_sum]

theorem nfDomPtwC_of_open (hT : NFTieHatC) (hH : NFHatProdKBS) : NFDomPtwC :=
  nfDomPtwC_of_cut unfolding_top_term_holds vector_multiplication_holds truncated_supremum_bound_holds leibniz_vector_estimate_holds
    (nFCoreNC_of_cut leibniz_vector_estimate_holds hT hH trace_norm_bound_constant_one operator_multiplication_admissible) empty_operator_list_holds

end

end CompanionTheory.NFCpt
