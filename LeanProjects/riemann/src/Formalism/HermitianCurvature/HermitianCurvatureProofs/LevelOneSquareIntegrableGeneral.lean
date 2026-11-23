import Formalism.HermitianCurvature.HermitianCurvatureProofs.DerivCombIntAllOfLevT

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fsv_add (s s' t : ℂ) : fsv s t * fsv s' t = fsv (s + s') t := by
  unfold fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add]
  ring

theorem fsv_zero (t : ℂ) : fsv 0 t = 1 := by
  simp [fsv]

section WaveJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)

def IsWaveJ (Ψ : RadSp P.k P.r z z' π π') : Prop :=
  Ψ ∈ lcSub P.k P.r z z' π π' ∧ ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)), 0 < ε ∧ JC.NiceCoef D ε G ∧
    ∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      fsv s (y.1 l) • resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2

def waveJ : Submodule ℂ (RadSp P.k P.r z z' π π') :=
  Submodule.span ℂ {Ψ | IsWaveJ P z z' π π' D l Ψ}

theorem waveJ_wave {Wv : Module.End ℂ (RadSp P.k P.r z z' π π')} {s : ℂ} (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) :
    ∀ Ψ ∈ waveJ P z z' π π' D l, Wv Ψ ∈ waveJ P z z' π π' D l := by
  intro Ψ hΨ
  unfold waveJ at hΨ ⊢
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨hlc, s0, ε, G, hε, hN, hval⟩ := hx
    apply Submodule.subset_span
    show IsWaveJ P z z' π π' D l (Wv x)
    unfold IsWaveJ
    refine ⟨fun c0 hc0 => ?_, s + s0, ε, G, hε, hN, fun y hy => ?_⟩
    · obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hlc c0 hc0
      exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' g hg hgK => by rw [hW x c' g, hK0 c' hc' g hg hgK, smul_zero]⟩
    · rw [hW x y.1 y.2, hval y hy, smul_smul, fsv_add]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end WaveJ

section Her

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem isWaveJ_jf (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π') (hz : D.z = z)
    (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    IsWaveJ P z z' π π' D l Φ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, ?_⟩
  obtain ⟨ε, hε, hG⟩ := hF.1.2
  refine ⟨0, ε, F, hε, ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hF.1.1 0 m).choose_spec.1), hF.1.1,
    fun g hg hne => by rw [hz, hz']; exact hG g hg hne⟩, fun y hy => ?_⟩
  rw [fsv_zero, one_smul]
  exact hΦ y hy

theorem herKc0_le_waveJ (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.castSucc = 0) :
    herKc S P z z' π π' L st l0 D 0 ≤ waveJ P z z' π π' D l := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ waveJ P z z' π π' D l := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ =>
      exact fun _ => Submodule.subset_span (isWaveJ_jf P z z' π π' D hD.1 hz hz' hπ hπ' l F hF Φ hΦ)
    | slice l' w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l')
    | waveC l' w' s Wv Wv' a' b' Φ _ h1 _ _ ih =>
      intro h
      have hll : l' = l := Fin.castSucc_injective _ (h.trans hl.symm)
      subst hll
      have hv := ih h
      have hVw : Vw (mkP Wv Wv') s w' a' b' = mkP Wv Wv' * UUiw s w' a' b' := by
        unfold Vw; exact io_apply_mul _ _ _ _
      obtain ⟨κ, hκ⟩ := mem_bot_alg (UUiw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w' a' b')
      have e : (Vw (mkP Wv Wv') s w' a' b').1 Φ = κ • Wv Φ := by
        rw [hVw, hκ, pr_fst_mul, pr_fst_algebraMap, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
        rfl
      rw [e]
      exact (waveJ P z z' π π' D l').smul_mem κ (waveJ_wave P z z' π π' D l' h1 Φ hv)
    | waveZ w s Wv Wv' a b Φ _ _ _ _ _ =>
      intro h
      exfalso
      have h0 := congrArg Fin.val h
      have h1 := congrArg Fin.val hl
      simp only [Fin.val_last, Fin.val_zero, Fin.val_castSucc] at h0 h1
      have := l.isLt
      omega
  exact key 0 Φ hΦ rfl

theorem rr_pic (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (ε : ℝ) (hε : 0 < ε) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hN : JC.NiceCoef D ε G)
    (Φ : RadSp P.k P.r z z' π π')
    (hΦ : ∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2)
    (w : List (Letter ℂ S)) (a b : Ix S) :
    ∃ G' : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G' ∧ ∀ y ∈ DomR P.k P.r z z',
      ((((RRi L st 0 w) a b).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G') y.1 y.2 := by
  subst hz hz' hπ hπ'
  let F' : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => if b' = b then G else fun _ => 0
  have hN' : ∀ b', JC.NiceCoef D ε (F' b') := by
    intro b'
    by_cases h : b' = b
    · simp only [F', if_pos h]; exact hN
    · simp only [F', if_neg h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let x : Ix S → Mx P.k P.r → (Wq →L[ℂ] Wp) := fun b' => B.JF D (F' b')
  let Φv : Ix S → RadSp P.k P.r D.z D.z' D.π D.π' := fun b' => if b' = b then Φ else 0
  have hx : ∀ b', x b' ∈ FFl P.k P.r D.z D.z' D.π D.π' 0 (OmPlus P.k P.r D.z D.z') := fun b' =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class P.k P.r Wp Wq D (F' b') ε hε (hN' b')
  have hΦv : ∀ b', ∀ y ∈ DomR P.k P.r D.z D.z',
      (Φv b' : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (x b') y.1 y.2 := by
    intro b' y hy
    by_cases h : b' = b
    · simp only [Φv, x, F', if_pos h]; exact hΦ y hy
    · simp only [Φv, x, F', if_neg h]
      simp only [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero, smul_zero]
      rfl
  have key := Formalism.FourierDecayAlt.P.JCx2.rma_main D.z_mem D.z'_mem X L st (M.sgn P l0) hD.2.2.1 hD.2.2.2.1 w x Φv hx hΦv
  have hsingle : act (RRi L st 0 w) Φv a = ((RRi L st 0 w) a b).1 Φ := by
    unfold act
    rw [Finset.sum_eq_single b (fun b' _ hb' => by simp only [Φv, if_neg hb', map_zero])
      (fun h => absurd (Finset.mem_univ b) h)]
    simp only [Φv, if_pos rfl]
  have hR := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure Formalism.FourierDecayAlt.P.JCx2.bcGood_closed
    (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0))
    (fun Y p q => Formalism.FourierDecayAlt.P.JCx2.bcGood_tL (Bs := D) (ε := ε) (M.sgn P l0) Y p q) w
  refine ⟨Formalism.FourierDecayAlt.D.actOp (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w) F' a, ?_, ?_⟩
  · show JC.NiceCoef D ε (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b'))
    exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' Finset.univ _ fun b' _ => (hR a b').1 (F' b') (hN' b')
  · intro y hy
    rw [← hsingle, key a y hy]
    have hGV : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ B.GV P.k P.r := by
      rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq]
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.QuantumDeterminants.big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
    have hh : wCell P.k P.r (Fin.last _) y.1 * y.2 ∈ JF.Om P.k P.r D.z D.z' :=
      ⟨hGV, Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hy.1 hy.2.1 hy.2.2⟩
    simp only [resG]
    congr 1
    exact (Formalism.FourierDecayAlt.P.JCx2.bc_core _ hR F' hN' a hh).symm

theorem rr_waveJ (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.castSucc = 0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (a b : Ix S) :
    ∀ Ψ ∈ waveJ P z z' π π' D l, ((RRi L st 0 w) a b).1 Ψ ∈ waveJ P z z' π π' D l := by
  have hRRlc := RRi_lc X μ L st l0 hD 0 w hw.1.2.1
  have hbase : ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ lcSub P.k P.r z z' π π' → ∀ (ε : ℝ), 0 < ε →
      ∀ G, JC.NiceCoef D ε G → (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) → ∀ c d, ((RRi L st 0 w) c d).1 Φ ∈ waveJ P z z' π π' D l := by
    intro Φ hlc ε hε G hN hΦ c d
    obtain ⟨G', hN', hpic⟩ := rr_pic P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' ε hε G hN Φ hΦ w c d
    refine Submodule.subset_span ⟨(hRRlc c d).1 Φ hlc, 0, ε, G', hε, hN', fun y hy => ?_⟩
    rw [fsv_zero, one_smul]
    exact hpic y hy
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Ψ hx =>
    obtain ⟨hlc, s, ε, G, hε, hN, hv⟩ := hx
    obtain ⟨Wv, hWv⟩ := Formalism.FourierDecayAlt.P5.waveCExists Wp Wq P.k P.r z z' π π' l s
    obtain ⟨Wv', hWv'⟩ := Formalism.FourierDecayAlt.P5.waveCExists Wp Wq P.k P.r z z' π π' l (-s)
    set Φ := Wv' Ψ with hΦdef
    have hΦlc : Φ ∈ lcSub P.k P.r z z' π π' := mul_lc hWv' Ψ hlc
    have hΦ : ∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
      intro y hy
      rw [hΦdef, hWv' Ψ y.1 y.2, hv y hy, smul_smul, fsv_neg_mul_fsv, one_smul]
    have hΨΦ : Ψ = Wv Φ := by
      apply Subtype.ext
      funext c g
      show (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
      by_cases hy : (c, g) ∈ DomR P.k P.r z z'
      · rw [hWv Φ c g, hΦ (c, g) hy, hv (c, g) hy]
      · rw [radSp_zero_off Ψ (x := (c, g)) hy, radSp_zero_off (Wv Φ) (x := (c, g)) hy]
    have hC := Formalism.FourierDecayAlt.P5.waveCommQQAll Wp Wq P z z' π π' X μ L st l0 hD l s Wv Wv' hWv hWv'
    have hWQ := waveQQ_castSucc X L st hD.2.2.1 l s Wv Wv' hWv hWv' hC
    rw [hl] at hWQ
    obtain ⟨hWave, -⟩ := Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hD.2.2.1 l s Wv Wv' hWv hWv'
    have hrr := rr_io_wave (QQi L st 0) (mkP Wv Wv') (mkP Wv' Wv) s w hWave hWQ hw.1.1
    have he := congrFun (congrFun hrr a) b
    rw [mul_io_apply, io_apply_mul] at he
    have hM : ((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b) ∈
        sendsTo (waveJ P z z' π π' D l) Φ := by
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun d _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Submodule.sum_mem _ fun c _ => ?_
      obtain ⟨α, hα⟩ := mem_bot_alg (star_entSub (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w) a c)
      obtain ⟨β, hβ⟩ := mem_bot_alg (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w d b)
      rw [hα, hβ]
      exact sendsTo_alg_mul_alg _ Φ (hbase Φ hΦlc ε hε G hN hΦ c d) α β
    have e : ((RRi L st 0 w) a b).1 (Wv Φ) =
        Wv (((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b).1 Φ) :=
      congrArg (fun x : Pr (RadSp P.k P.r z z' π π') => x.1 Φ) he
    rw [hΨΦ, e]
    exact waveJ_wave P z z' π π' D l hWv _ hM
  | zero => rw [map_zero]; exact (waveJ P z z' π π' D l).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (waveJ P z z' π π' D l).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (waveJ P z z' π π' D l).smul_mem c hx

theorem unwave (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r) (Ψ : RadSp P.k P.r z z' π π')
    (hΨ : IsWaveJ P z z' π π' D l Ψ) :
    ∃ (s : ℂ) (ε : ℝ) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π')
      (Wv : Module.End ℂ (RadSp P.k P.r z z' π π')), 0 < ε ∧ JC.NiceCoef D ε G ∧ Φ ∈ lcSub P.k P.r z z' π π' ∧
      (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) ∧ multiplicationOperator Wv (fun c _ => fsv s (c l)) ∧ Ψ = Wv Φ := by
  obtain ⟨hlc, s, ε, G, hε, hN, hval⟩ := hΨ
  obtain ⟨Wv, hWv⟩ := waveCExists Wp Wq P.k P.r z z' π π' l s
  obtain ⟨Wv', hWv'⟩ := waveCExists Wp Wq P.k P.r z z' π π' l (-s)
  have e1 : -s + s = 0 := by ring
  have e2 : s + -s = 0 := by ring
  refine ⟨s, ε, G, Wv' Ψ, Wv, hε, hN, fun c0 hc0 => ?_, fun y hy => ?_, hWv, ?_⟩
  · obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hlc c0 hc0
    exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' g hg hgK => by rw [hWv' Ψ c' g, hK0 c' hc' g hg hgK, smul_zero]⟩
  · rw [hWv' Ψ y.1 y.2, hval y hy, smul_smul, fsv_add, e1, fsv_zero, one_smul]
  · apply Subtype.ext
    funext c g
    rw [hWv (Wv' Ψ) c g, hWv' Ψ c g, smul_smul, fsv_add, e2, fsv_zero, one_smul]

end Her

section Fs

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def fs (μ : Measure (Mt k r)) (l : Fin r) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) : ℂ :=
  ∫ c' : Cf r l.succ, wtI l.succ c' * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) c')

def GoodL (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (u : RadSp k r z z' π π') : Prop :=
  u ∈ lcSub k r z z' π π' ∧ ∀ t : ℂ, t ≠ 0 → LevelSquareIntegrable μ l.succ u (Function.update c l t)

variable (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r) (c : Fin r → ℂ)

include hμ in
theorem pairAt_add_left_lc {u1 u2 v : RadSp k r z z' π π'} (h1 : u1 ∈ lcSub k r z z' π π')
    (h2 : u2 ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ (u1 + u2) v p = pairAt μ u1 v p + pairAt μ u2 v p := by
  have hadd : ∀ A A' C : Wq →L[ℂ] Wp, B.hsInner (A + A') C = B.hsInner A C + B.hsInner A' C := by
    intro A A' C
    simp [B.hsInner, B.hsVec, PiLp.inner_apply, inner_add_right, Finset.sum_add_distrib]
  unfold pairAt
  rw [← integral_add (int_lc μ hμ h1 hv p) (int_lc μ hμ h2 hv p)]
  congr 1
  ext x
  simp only [Submodule.coe_add, Pi.add_apply, hadd]

include hμ in
theorem goodL_add {u v : RadSp k r z z' π π'} (hu : GoodL μ l c u) (hv : GoodL μ l c v) : GoodL μ l c (u + v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨Submodule.add_mem _ hu1 hv1, fun t ht => ?_⟩
  have hw : Measurable (fun c' : Cf r l.succ => wtI l.succ c') := by
    unfold wtI
    first | fun_prop | measurability
  have cross : ∀ a b : RadSp k r z z' π π', a ∈ lcSub k r z z' π π' → b ∈ lcSub k r z z' π π' →
      LevelSquareIntegrable μ l.succ a (Function.update c l t) → LevelSquareIntegrable μ l.succ b (Function.update c l t) →
      Integrable (fun c' : Cf r l.succ => wtI l.succ c' * pairAt μ a b (glue l.succ (Function.update c l t) c')) := by
    intro a b ha hb ia ib
    refine Integrable.mono' (Integrable.add (Integrable.norm ia) (Integrable.norm ib)) ?_ (ae_of_all _ fun c' => ?_)
    · exact hw.aestronglyMeasurable.mul (pairAt_measI μ l.succ a b _).aestronglyMeasurable
    · simp only [Pi.add_apply, norm_mul]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ ha hb _) (norm_nonneg _)
  unfold LevelSquareIntegrable
  refine Integrable.congr (Integrable.add (Integrable.add (Integrable.add (hu2 t ht) (cross u v hu1 hv1 (hu2 t ht) (hv2 t ht)))
    (cross v u hv1 hu1 (hv2 t ht) (hu2 t ht))) (hv2 t ht)) (ae_of_all _ fun c' => ?_)
  simp only [Pi.add_apply]
  rw [pairAt_add_add μ hμ hu1 hv1]
  ring

private theorem hsInner_smul_lemma (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner (a • A) C = a * B.hsInner A C := by
  simp [B.hsInner, B.hsVec, PiLp.inner_apply, inner_smul_right, Finset.mul_sum]

private theorem hsInner_smul_lemma_2 (a : ℂ) (A C : Wq →L[ℂ] Wp) : B.hsInner A (a • C) = conj a * B.hsInner A C := by
  simp [B.hsInner, B.hsVec, PiLp.inner_apply, inner_smul_left, Finset.mul_sum]

private theorem pairAt_smul_lemma_3 (a : ℂ) (u v : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ (a • u) v p = a * pairAt μ u v p := by
  unfold pairAt
  simp only [Submodule.coe_smul, Pi.smul_apply, hsInner_smul_lemma]
  exact integral_const_mul a _

private theorem pairAt_smul_lemma_4 (a : ℂ) (u v : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ u (a • v) p = conj a * pairAt μ u v p := by
  unfold pairAt
  simp only [Submodule.coe_smul, Pi.smul_apply, hsInner_smul_lemma_2]
  exact integral_const_mul _ _

theorem goodL_smul {u : RadSp k r z z' π π'} (a : ℂ) (hu : GoodL μ l c u) : GoodL μ l c (a • u) := by
  obtain ⟨hlc, hL2⟩ := hu
  refine ⟨Submodule.smul_mem _ a hlc, fun t ht => ?_⟩
  have h := Integrable.const_mul (hL2 t ht) (a * conj a)
  unfold LevelSquareIntegrable
  refine h.congr (ae_of_all _ fun c' => ?_)
  simp only [pairAt_smul_lemma_3, pairAt_smul_lemma_4]
  ring

theorem goodL_zero : GoodL μ l c (0 : RadSp k r z z' π π') := by
  refine ⟨Submodule.zero_mem _, fun t _ => ?_⟩
  unfold LevelSquareIntegrable
  refine (integrable_zero _ _ _).congr (ae_of_all _ fun c' => ?_)
  have h := pairAt_smul_lemma_3 μ (0 : ℂ) (0 : RadSp k r z z' π π') 0 (glue l.succ (Function.update c l t) c')
  rw [zero_smul, zero_mul] at h
  simp [h]

private theorem pairAt_mul_lemma_6 {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ}
    (hW : multiplicationOperator W m) (hm : ∀ c g, ‖m c g‖ = 1) (u : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ (W u) (W u) p = pairAt μ u u p := by
  unfold pairAt
  congr 1
  ext x
  rw [hW u p, hsInner_smul_lemma, hsInner_smul_lemma_2, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]
  simp

theorem goodL_mul {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) {u : RadSp k r z z' π π'} (hu : GoodL μ l c u) : GoodL μ l c (W u) := by
  obtain ⟨hlc, hL2⟩ := hu
  refine ⟨fun c0 hc0 => ?_, fun t ht => ?_⟩
  · obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hlc c0 hc0
    exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' g hg hgK => by rw [hW u c' g, hK0 c' hc' g hg hgK, smul_zero]⟩
  · have h := hL2 t ht
    unfold LevelSquareIntegrable at h ⊢
    simpa only [pairAt_mul_lemma_6 μ hW hm] using h

include hμ in
theorem fs_add_left {u1 u2 v : RadSp k r z z' π π'} (h1 : GoodL μ l c u1) (h2 : GoodL μ l c u2)
    (hv : GoodL μ l c v) {t : ℂ} (ht : t ≠ 0) : fs μ l (u1 + u2) v c t = fs μ l u1 v c t + fs μ l u2 v c t := by
  obtain ⟨h1l, h1L⟩ := h1
  obtain ⟨h2l, h2L⟩ := h2
  obtain ⟨hvl, hvL⟩ := hv
  have hw : Measurable (fun c' : Cf r l.succ => wtI l.succ c') := by
    unfold wtI
    first | fun_prop | measurability
  have cross : ∀ a b : RadSp k r z z' π π', a ∈ lcSub k r z z' π π' → b ∈ lcSub k r z z' π π' →
      LevelSquareIntegrable μ l.succ a (Function.update c l t) → LevelSquareIntegrable μ l.succ b (Function.update c l t) →
      Integrable (fun c' : Cf r l.succ => wtI l.succ c' * pairAt μ a b (glue l.succ (Function.update c l t) c')) := by
    intro a b ha hb ia ib
    refine Integrable.mono' (Integrable.add (Integrable.norm ia) (Integrable.norm ib)) ?_ (ae_of_all _ fun c' => ?_)
    · exact hw.aestronglyMeasurable.mul (pairAt_measI μ l.succ a b _).aestronglyMeasurable
    · simp only [Pi.add_apply, norm_mul]
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ ha hb _) (norm_nonneg _)
  unfold fs
  rw [← integral_add (cross u1 v h1l hvl (h1L t ht) (hvL t ht)) (cross u2 v h2l hvl (h2L t ht) (hvL t ht))]
  congr 1
  ext c'
  rw [pairAt_add_left_lc μ hμ h1l h2l hvl, mul_add]

theorem fs_smul_left (u v : RadSp k r z z' π π') (a : ℂ) (t : ℂ) : fs μ l (a • u) v c t = a * fs μ l u v c t := by
  unfold fs
  rw [← integral_const_mul]
  congr 1
  ext c'
  rw [pairAt_smul_lemma_3]
  ring

private theorem pairAt_swap_lemma_5 (u v : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ v u p = conj (pairAt μ u v p) := by
  unfold pairAt
  rw [← integral_conj]
  congr 1
  ext x
  simp only [B.hsInner]
  exact (inner_conj_symm _ _).symm

theorem fs_swap (u v : RadSp k r z z' π π') (t : ℂ) : fs μ l v u c t = conj (fs μ l u v c t) := by
  unfold fs
  rw [← integral_conj]
  congr 1
  ext c'
  rw [map_mul, pairAt_swap_lemma_5]
  congr 1
  simp [wtI]

theorem fs_zero_left (v : RadSp k r z z' π π') (t : ℂ) : fs μ l 0 v c t = 0 := by
  simpa using fs_smul_left μ l c 0 v 0 t

private theorem pairAt_wave_lemma_7 {W1 W2 : Module.End ℂ (RadSp k r z z' π π')} {s1 s2 : ℂ}
    (h1 : multiplicationOperator W1 (fun c _ => fsv s1 (c l))) (h2 : multiplicationOperator W2 (fun c _ => fsv s2 (c l)))
    (Φ1 Φ2 : RadSp k r z z' π π') (p : Fin r → ℂ) :
    pairAt μ (W1 Φ1) (W2 Φ2) p = fsv s1 (p l) * conj (fsv s2 (p l)) * pairAt μ Φ1 Φ2 p := by
  unfold pairAt
  rw [← integral_const_mul]
  congr 1
  ext x
  simp only [h1 Φ1 p, h2 Φ2 p, hsInner_smul_lemma, hsInner_smul_lemma_2]
  ring

theorem fs_wave {W1 W2 : Module.End ℂ (RadSp k r z z' π π')} {s1 s2 : ℂ}
    (h1 : multiplicationOperator W1 (fun c _ => fsv s1 (c l))) (h2 : multiplicationOperator W2 (fun c _ => fsv s2 (c l)))
    (Φ1 Φ2 : RadSp k r z z' π π') (t : ℂ) :
    fs μ l (W1 Φ1) (W2 Φ2) c t = fsv s1 t * conj (fsv s2 t) * fs μ l Φ1 Φ2 c t := by
  unfold fs
  rw [← integral_const_mul]
  congr 1
  ext c'
  have hg : glue l.succ (Function.update c l t) c' l = t := by
    simp [glue, Fin.val_succ]
  rw [pairAt_wave_lemma_7 μ l h1 h2, hg]
  ring

end Fs

def LevelOneSquareIntegrableGeneral : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.castSucc = 0 → ∀ (ε : ℝ), 0 < ε → ∀ G : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G →
    ∀ Φ : RadSp P.k P.r z z' π π', Φ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    ∀ c ∈ OmX P.r, ∀ t : ℂ, t ≠ 0 → LevelSquareIntegrable μ l.succ Φ (Function.update c l t)

def ContLev1Gen : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.castSucc = 0 → ∀ (ε ε' : ℝ), 0 < ε → 0 < ε' → ∀ G H : Mx P.k P.r → (Wq →L[ℂ] Wp),
    JC.NiceCoef D ε G → JC.NiceCoef D ε' H → ∀ Φ Ψ : RadSp P.k P.r z z' π π',
    Φ ∈ lcSub P.k P.r z z' π π' → Ψ ∈ lcSub P.k P.r z z' π π' →
    (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) →
    (∀ y ∈ DomR P.k P.r z z', (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D H) y.1 y.2) →
    ∀ c ∈ OmX P.r, ContinuousOn (fun t => fs μ l Φ Ψ c t) {0}ᶜ

def ContDens0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x v : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) v →
      ∀ c ∈ OmX P.r, ∀ n : ℕ, ∀ t, t ≠ 0 → ContinuousAt (Dens μ l (act (RRi L st l.castSucc w) x) v c) t

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem contDens0_of (hL2 : LevelOneSquareIntegrableGeneral) (hC : ContLev1Gen) : ContDens0 := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD _ _ hz hz' hπ hπ' w hw l hl x v hx hv c hc _ t ht
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  have hl0 : l.castSucc = 0 := Fin.ext (by simp [hl])
  rw [hl0] at hx hv ⊢
  have hle := herKc0_le_waveJ (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0

  have hgood : ∀ u ∈ waveJ P z z' π π' D l, GoodL μ l c u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨s, ε, G, Φ, Wv, hε, hN, hlc, hpic, hWv, rfl⟩ := unwave P z z' π π' D l u hu
      exact goodL_mul μ l c hWv (fun _ _ => norm_fsv _ _)
        ⟨hlc, fun t ht => hL2 Wp Wq P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0 ε hε G hN Φ hlc hpic c hc t ht⟩
    | zero => exact goodL_zero μ l c
    | add u1 u2 _ _ h1 h2 => exact goodL_add μ hD.2.1 l c h1 h2
    | smul a u _ h => exact goodL_smul μ l c a h

  have hcont : ∀ u ∈ waveJ P z z' π π' D l, ∀ v' ∈ waveJ P z z' π π' D l,
      ContinuousOn (fun t => fs μ l u v' c t) {0}ᶜ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      intro v' hv'
      induction hv' using Submodule.span_induction with
      | mem v' hv' =>
        obtain ⟨s, ε, G, Φ, Wv, hε, hN, hlc, hpic, hWv, rfl⟩ := unwave P z z' π π' D l u hu
        obtain ⟨s', ε', G', Φ', Wv', hε', hN', hlc', hpic', hWv', rfl⟩ := unwave P z z' π π' D l v' hv'
        have e : (fun t => fs μ l (Wv Φ) (Wv' Φ') c t) = fun t => fsv s t * conj (fsv s' t) * fs μ l Φ Φ' c t :=
          funext fun t => fs_wave μ l c hWv hWv' Φ Φ' t
        rw [e]
        refine (((contDiff_fsv s).continuous.mul (Complex.continuous_conj.comp (contDiff_fsv s').continuous))
          ).continuousOn.mul ?_
        exact hC Wp Wq P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0 ε ε' hε hε' G G' hN hN' Φ Φ' hlc hlc'
          hpic hpic' c hc
      | zero =>
        have e : (fun t => fs μ l u 0 c t) = fun _ => 0 := funext fun t => by
          rw [fs_swap, fs_zero_left, map_zero]
        rw [e]; exact continuousOn_const
      | add v1 v2 hv1 hv2 h1 h2 =>
        have hu' := hgood u (Submodule.subset_span hu)
        refine ((h1.add h2)).congr fun t ht => ?_
        show fs μ l u (v1 + v2) c t = fs μ l u v1 c t + fs μ l u v2 c t
        rw [fs_swap, fs_add_left μ hD.2.1 l c (hgood v1 hv1) (hgood v2 hv2) hu' ht, map_add, ← fs_swap, ← fs_swap]
      | smul a v' _ h =>
        refine ((continuousOn_const (c := (starRingEnd ℂ) a)).mul h).congr fun t _ => ?_
        show fs μ l u (a • v') c t = conj a * fs μ l u v' c t
        rw [fs_swap, fs_smul_left, map_mul, ← fs_swap]
    | zero =>
      intro v' _
      have e : (fun t => fs μ l 0 v' c t) = fun _ => 0 := funext fun t => fs_zero_left μ l c v' t
      rw [e]; exact continuousOn_const
    | add u1 u2 hu1 hu2 h1 h2 =>
      intro v' hv'
      refine ((h1 v' hv').add (h2 v' hv')).congr fun t ht => ?_
      exact fs_add_left μ hD.2.1 l c (hgood u1 hu1) (hgood u2 hu2) (hgood v' hv') ht
    | smul a u _ h =>
      intro v' hv'
      exact ((continuousOn_const (c := a)).mul (h v' hv')).congr fun t _ => fs_smul_left μ l c u v' a t

  have hu : ∀ a, act (RRi L st 0 w) x a ∈ waveJ P z z' π π' D l := fun a => by
    show ∑ b, ((RRi L st 0 w) a b).1 (x b) ∈ waveJ P z z' π π' D l
    exact Submodule.sum_mem _ fun b _ =>
      rr_waveJ P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0 w hw a b (x b) (hle (hx b))
  have hv' : ∀ a, v a ∈ waveJ P z z' π π' D l := fun a => hle (hv a)

  have hD' : ∀ t', t' ≠ 0 → Dens μ l (act (RRi L st 0 w) x) v c t' =
      ((‖t'‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, fs μ l (act (RRi L st 0 w) x a) (v a) c t' := by
    intro t' ht'
    unfold Dens form fs
    congr 1
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun a _ =>
      int_crossI μ hD.2.1 l.succ (hgood _ (hu a)).1 (hgood _ (hv' a)).1 _ ((hgood _ (hu a)).2 t' ht')
        ((hgood _ (hv' a)).2 t' ht')
  have hon : ContinuousOn (fun t' => ((‖t'‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, fs μ l (act (RRi L st 0 w) x a) (v a) c t') {0}ᶜ := by
    refine ContinuousOn.mul ?_ (continuousOn_finset_sum _ fun a _ => hcont _ (hu a) _ (hv' a))
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (continuous_norm.continuousOn).zpow₀ (-2) fun t' ht' => Or.inl (norm_ne_zero_iff.mpr ht')
  have hat := (hon.continuousAt (isOpen_compl_singleton.mem_nhds ht))
  refine hat.congr ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds ht] with t' ht'
  exact (hD' t' ht').symm

end Red

end Formalism.FourierDecayAlt.P5.HerD
