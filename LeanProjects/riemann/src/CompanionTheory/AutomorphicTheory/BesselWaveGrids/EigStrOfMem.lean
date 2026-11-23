import CompanionTheory.AutomorphicTheory.BesselWaveGrids.KDecayOfGap

noncomputable section

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants
open CompanionTheory.LimBd.Main (GfPoly SpanPow CoefSmooth CoefCC CoefEig PhZero BetaInfZero ZuckT ZuckDualT Box KDecay Wsp
  Letters wsp_ckOn wsp_inCC wsp_eig wsp_orth smul_mem_iSup gap_of_box norm_capP_le)
open CompanionTheory.WaveGrid.Coef

section w

variable {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {ε : Fin (2 * r + k + 1) → Bool} {μ : Fin (2 * r + k + 1) → ℝ}

theorem w_inCC (hK : PI.KFinSmooth) (hC : CoefCC) {A h : ℝ} (hD : KDecay k r ε A h)
    (hg : PI.ZuckTensor.GapAtLeast ε μ h) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : F ∈ Wsp k r Wp Wq ε μ) (m : ℕ) :
    B.InCC A m F := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    exact hC hK k r ε A h hD μ φ _ T m hφ hg
  | zero => exact JCx2.sq_inCC_zero
  | add F F' _ _ h h' => exact JCx2.sq_inCC_add h h'
  | smul c F _ h => exact JCx2.sq_inCC_smul c h

theorem mul_mem_box (h2 : SpanPow) {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) {h : ℝ} {d : ℕ}
    {q : B.Mat k r → ℂ} (hq : q ∈ Letters k r ^ d) (hg : PI.ZuckTensor.GapAtLeast ε μ h)
    (ht : t _ ε + 1 + 2 * (d : ℝ) < h) (L : Wq' →L[ℂ] Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : F ∈ Wsp k r Wp Wq ε μ) :
    (fun g => q g • (F g).comp L) ∈ ⨆ ν : Box μ (d : ℝ), Wsp k r Wp Wq' ε ν := by
  induction hF using Submodule.span_induction with
  | mem F h' =>
    obtain ⟨φ, T, hφ, rfl⟩ := h'
    have := smul_mem_iSup (h2 t hZ hZd k r ε μ h d q φ hq hφ hg ht) (T.comp L)
    convert this using 2 with g
    rw [ContinuousLinearMap.smul_comp, smul_smul, Pi.mul_apply]
  | zero =>
    convert Submodule.zero_mem _ using 2 with g
    simp
  | add F F' _ _ h h' =>
    convert Submodule.add_mem _ h h' using 2 with g
    simp [ContinuousLinearMap.add_comp]
  | smul c F _ h =>
    convert Submodule.smul_mem _ c h using 2 with g
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_comp]
    rw [smul_comm]

end w

section place

variable {P : M.Par} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wq']

theorem w_ffkb (hK : PI.KFinSmooth) (hS : CoefSmooth) (hE : CoefEig) (hB : SmoothKB)
    (p : KB.Pl P Wp Wq) {ε : Fin (2 * P.r + P.k + 1) → Bool} {μ : Fin (2 * P.r + P.k + 1) → ℝ}
    {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hf : f ∈ Wsp P.k P.r Wp Wq ε μ) {A : ℝ}
    (hA : ∀ m, m ≤ CompanionTheory.JfS.NN P.k P.r → JF.TransportedAlt P.k P.r A m) (hcc : ∀ m : ℕ, B.InCC A m f) :
    B.JF p.T.base f ∈ FFKB p := by
  have hs := hB P Wp Wq p f A hA (wsp_ckOn hK hS hf) hcc fun Y => ⟨_, wsp_eig hK hS hE _ hf⟩
  exact EqShift.jf_ff_of_smooth p.T.base f (OmKB p) fun g₀ hg₀ =>
    hs g₀ ⟨hg₀.1, (CutMP.jdc_om_of _ _ hg₀.1.1 hg₀.2).2⟩

theorem eigStr_of_mem (h3 : CoefSmooth) (h4 : CoefCC) (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero)
    (hK : PI.KFinSmooth) (p : KB.Pl P Wp Wq) (F F₁ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ d : ℝ}
    (hF₁ : F₁ ∈ ⨆ ν : Box lam d, Wsp P.k P.r Wp Wq ε ν) (hFF : ∀ g ∈ B.GV P.k P.r, F g = F₁ g)
    (hgap : PI.ZuckTensor.GapAtLeast ε lam h) (hA : B.AB P.k P.r ≤ A) (hD : KDecay P.k P.r ε A h₀)
    (hh : h₀ + 2 * d ≤ h) (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam d y ≤ nn y) : EigStr p nn F Y := by
  classical
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ F₁).1 hF₁
  let e := c.support.equivFin.symm
  have hgν : ∀ ν : Box lam d, PI.ZuckTensor.GapAtLeast ε ν.1 h₀ := fun ν => gap_of_box ν.2 hgap hh
  have hFs : ∀ g ∈ B.GV P.k P.r, F g = ∑ i, c (e i) g := by
    intro g hg
    rw [hFF g hg, ← hsum, Finsupp.sum, Finset.sum_apply, ← Finset.sum_coe_sort]
    exact (Equiv.sum_comp e fun ν : c.support => c ν g).symm
  exact ⟨A, c.support.card, fun i => c (e i), fun i y => Formalism.QuantumDeterminants.capP (fun s => ((e i).1.1 s : ℂ)) (y : ℂ), hA,
    fun i => wsp_ckOn hK h3 (hc _), fun i => wsp_inCC hK h4 hD (hgν _) (hc _), hFs,
    fun i y _ => wsp_eig hK h3 h5 _ (hc _), fun i y hy => (norm_capP_le (e i).1.2 y).trans (hnn y hy),
    fun i j hij => wsp_orth hK h4 h5 h6 h7 _ hA hD (hgν _) (hgν _)
      (fun hh' => hij (e.injective (Subtype.ext (Subtype.ext hh')))) (hc _) (hc _)⟩

theorem eigStr_fpmW (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : f ∈ Wsp P.k P.r Wp Wq ε lam) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A) (hD : KDecay P.k P.r ε A h₀)
    (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam (((2 * P.r + 2) * p₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y :=
  eigStr_of_mem h3 h4 h5 h6 h7 hK p _ _ nn Y
    (mul_mem_box h2 hZ hZd (h1 P.k P.r p.T.base.z p.T.base.z' p₀) hgap ht (ContinuousLinearMap.id ℂ Wq) hf)
    (fun _ _ => rfl) hgap hA hD hh hnn

theorem eigStr_fpmShW {u u' : ℕ → ℝ} (h1 : GfPoly) (h2 : SpanPow) (h3 : CoefSmooth) (h4 : CoefCC)
    (h5 : CoefEig) (h6 : PhZero) (h7 : BetaInfZero) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t)
    (p : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Aop : B.Mat P.k P.r → (Wq' →L[ℂ] Wq))
    (p₀ e₀ : ℕ) (nn : ℝ → ℝ) (Y : Finset ℝ)
    {ε : Fin (2 * P.r + P.k + 1) → Bool} {lam : Fin (2 * P.r + P.k + 1) → ℝ} {A h h₀ : ℝ}
    (hf : f ∈ Wsp P.k P.r Wp Wq ε lam) (hAop : PolyOp e₀ Aop) (hgap : PI.ZuckTensor.GapAtLeast ε lam h)
    (ht : t _ ε + 1 + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) < h) (hA : B.AB P.k P.r ≤ A)
    (hD : KDecay P.k P.r ε A h₀) (hh : h₀ + 2 * (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) ≤ h)
    (hnn : ∀ y, LetPt Y y → CompanionTheory.LimBd.Main.PStar lam (((2 * P.r + 2) * p₀ + e₀ : ℕ) : ℝ) y ≤ nn y) :
    EigStr p nn (fpmSh p f Aop p₀) Y := by
  obtain ⟨n, cf, L, hcf, hAe⟩ := hAop
  set q : B.Mat P.k P.r → ℂ := fun g => ((Formalism.QuantumDeterminants.Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) with hq
  refine eigStr_of_mem h3 h4 h5 h6 h7 hK p _ (∑ i, fun g => (q * cf i) g • (f g).comp (L i)) nn Y
    (Submodule.sum_mem _ fun i _ => mul_mem_box h2 hZ hZd
      (LimSh.mul_mem_letters_pow (h1 P.k P.r _ _ p₀) (LimSh.polyDeg_mem (hcf i))) hgap ht (L i) hf)
    (fun g _ => ?_) hgap hA hD hh hnn
  show q g • (f g).comp (Aop g) = _
  rw [hAe g, ContinuousLinearMap.comp_finsetSum, Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_smul, smul_smul]
  rfl

end place

def EndDiffW (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ Cb C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      f ∈ Wsp P.k P.r Wp Wq ε lam' → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h → t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → HypType P.k P.r lam P.u' b →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      30 * ((P.r : ℝ) + 1) ^ 2 + 6 ≤ |P.u p.l0 - P.u' p.l0| →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) → ThmBpAt p f b C₄ 0 p₀

def EndEqW (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ C₃ CT C₀ : ℝ, 0 ≤ C₃ → 0 ≤ CT → 1 / 2 ≤ C₀ →
    ∃ C₄ CA : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] [CompleteSpace Wp] (P : M.Par)
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (p₀ n₀ l : ℕ)
      (lam lam' : Fin (2 * P.r + P.k + 1) → ℝ) (ε : Fin (2 * P.r + P.k + 1) → Bool) (c g e h : ℝ),
      f ∈ Wsp P.k P.r Wp Wq ε lam' → lam' ∈ Box lam e → e + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) ≤ c →
      PI.ZuckTensor.GapAtLeast ε lam' h →
      t _ ε + CA * thrX P.k P.r + 3 * (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) + 1 < h →
      HypLam P.k P.r lam c g b → HypType P.k P.r lam P.u b → P.u = P.u' →
      b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T' → 1 ≤ Tq p →
      n₀ = 30 * (P.r + 1) ^ 2 + 6 → 1 ≤ l → l < P.k → (2 * n₀ + 1 : ℝ) ≤ P.u l - P.u (l + 1) →
      3 * (P.r + 1) ≤ 2 * p₀ → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) → ThmBpAt p f b C₄ n₀ p₀

theorem endDiffW_of (hAsm : AsmDiff) (hS : LimSteps) (hB : SmoothKB) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) : EndDiffW t := by
  intro Cb C₃ CT C₀ hC₃ hCT hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', H⟩ := hAsm Cb C₃ (6 + CT) C₀ hC₃ (by linarith) hC₀
  set CA : ℝ := max (max (max c₃ Cc) (max Cc' Cc'')) 46 with hCA
  have k0 : 46 ≤ CA := le_max_right _ _
  have k1 : c₃ ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have k2 : Cc ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have k3 : Cc' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have k4 : Cc'' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  refine ⟨C₄, CA, ?_⟩
  intro Wp Wq _ _ _ _ _ _ _ P p f b p₀ lam lam' ε c g e h hfK hbox hec hgap hh hL hu hu' hTT hT hlen hN hp₀ hCb hexp
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hS
  have hd : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : 0 ≤ CA * thrX P.k P.r := mul_nonneg (by linarith) (thrX_nonneg _ _)
  have hD := kDecay_of_gap hZ P.k P.r ε hX hd hh
  have hfA := w_inCC hK s4 hD (gap_mono hgap (by linarith)) hfK
  have hXA : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hXA' : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by
    linarith
  have hc : 0 < c := by linarith [hL.c_ge]
  obtain ⟨hW, hLi⟩ := grids_diff p lam c g b hL hu hu' hlen
  obtain ⟨hΛ1, hΛ2⟩ := gridΛ_bounds p b CT hL.b_ge_three hCT hTT
  exact H Wp Wq P p f b _ _ p₀ Topx2.chi0 (PStar lam c) (gridY P p.l0 (3 * (P.r + 1))) 3 (3 * (P.r + 1)) hL.b_ge_three
    hΛ1 hΛ2 hT hp₀ le_rfl (by omega) Topx2.base_cutoff_is_truncation (PStar_pos lam hc) hCb (wsp_ckOn hK s3 hfK) hfA
    (w_ffkb hK s3 s5 hB p hfK (fun m hm => thr_JF _ _ m hm k0 hXA) hfA)
    (thr_conv _ _ k1 (by linarith) hXA') (thr_main _ _ k2 hXA') (thr_main _ _ k3 hXA') (thr_main _ _ k4 hXA') hN hexp
    hW hLi
    (limBd_of_eigStr p _ _ _ _ (eigStr_fpmW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd p f p₀ _ _ hfK hgap (by linarith)
      (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))

theorem endEqW_of (hAsm : AsmEq) (hW : WigExists) (hS : LimSteps) (hB : SmoothKB) (hK : PI.KFinSmooth)
    {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} (hZ : ZuckT t) (hZd : ZuckDualT t) : EndEqW t := by
  intro C₃ CT C₀ hC₃ hCT hC₀
  obtain ⟨Cb, c₅, -, hSh⟩ := EqShift.shiftAtR_full hW
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', H⟩ := hAsm Cb C₃ (6 + CT) C₀ hC₃ (by linarith) hC₀
  set CA : ℝ := max (max (max c₃ Cc) (max Cc' Cc'')) (max 46 c₅) with hCA
  have k0 : 46 ≤ CA := le_max_of_le_right (le_max_left _ _)
  have k5 : c₅ ≤ CA := le_max_of_le_right (le_max_right _ _)
  have k1 : c₃ ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
  have k2 : Cc ≤ CA := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
  have k3 : Cc' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_left _ _))
  have k4 : Cc'' ≤ CA := le_max_of_le_left (le_max_of_le_right (le_max_right _ _))
  refine ⟨C₄, CA, ?_⟩
  intro Wp Wq _ _ _ _ _ _ _ P p f b p₀ n₀ l lam lam' ε c g e h hfK hbox hec hgap hh hL hu huu hTT hT hn₀ hl1 hlk hposition
    hN hp₀ hexp
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hS
  have hd : (0 : ℝ) ≤ (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hX : 0 ≤ CA * thrX P.k P.r := mul_nonneg (by linarith) (thrX_nonneg _ _)
  have hD := kDecay_of_gap hZ P.k P.r ε hX hd hh
  have hfA := w_inCC hK s4 hD (gap_mono hgap (by linarith)) hfK
  have hXA : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) := by linarith
  have hXA' : CA * thrX P.k P.r ≤ CA * thrX P.k P.r + (((2 * P.r + 2) * p₀ + n₀ * (P.r + 1) : ℕ) : ℝ) -
      (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) := by
    rw [Nat.cast_add]
    linarith
  have hc : 0 < c := by linarith [hL.c_ge]
  have hJ := w_ffkb hK s3 s5 hB p hfK (fun m hm => thr_JF _ _ m hm k0 hXA) hfA
  obtain ⟨S, e1, e2, e3, e4, e5, e6, hDp, hDm, hJp, hJm⟩ := hSh P Wp Wq p f b n₀ l _ huu hl1 hlk (huu ▸ hposition)
    hL.b_ge_three (fun i hi => huu ▸ hu.u_le i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2)
    (thr_conv _ _ k5 (by linarith) hXA) (thr_JF _ _ _ (Nat.zero_le _) k0 hXA) (hfA 1) (hfA 0) hJ
  rw [← huu] at e2 e4
  obtain ⟨hWp, hLip⟩ := grids_plus S.pp lam c g b l n₀ hL hu hn₀ hl1 hlk hposition e1 e2 e5
  obtain ⟨hWm, hLim⟩ := grids_minus S.pm lam c g b l n₀ hL hu hn₀ hl1 hlk hposition e3 e4 e6
  obtain ⟨hΛ1, hΛ2⟩ := gridΛ_bounds p b CT hL.b_ge_three hCT hTT
  exact H P Wp Wq p f b n₀ S _ _ p₀ Topx2.chi0 (PStar lam c) (PStar lam c)
    (gridY (shP P S.up S.up') S.pp.l0 (3 * (P.r + 1))) (gridY (shP P S.um S.um') S.pm.l0 (3 * (P.r + 1))) 3
    (3 * (P.r + 1)) hL.b_ge_three hΛ1 hΛ2 hT hn₀.le hp₀ le_rfl (by omega) Topx2.base_cutoff_is_truncation (PStar_pos lam hc)
    (PStar_pos lam hc) hDp hDm (wsp_ckOn hK s3 hfK) hfA hJp hJm
    (thr_conv _ _ k1 (by linarith) hXA') (thr_main _ _ k2 hXA') (thr_main _ _ k3 hXA') (thr_main _ _ k4 hXA') hN hexp
    hWp hLip hWm hLim
    (limBd_of_eigStr S.pp _ _ _ _ (eigStr_fpmShW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd S.pp f S.Ap p₀ _ _ _ hfK S.polyP
      hgap (by linarith) (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))
    (limBd_of_eigStr S.pm _ _ _ _ (eigStr_fpmShW s1 s2 s3 s4 s5 s6 s7 hK hZ hZd S.pm f S.Am p₀ _ _ _ hfK S.polyM
      hgap (by linarith) (thr_AB _ _ k0 hXA) hD (by linarith) fun y _ => pStar_box hbox hd hec y))

end CompanionTheory.WaveGrid
