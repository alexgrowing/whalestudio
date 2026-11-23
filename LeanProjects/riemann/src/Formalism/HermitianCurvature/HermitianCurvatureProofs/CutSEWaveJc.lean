import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Supp

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def SuppLoc (Θ : (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ f g, g ∉ tsupport f → Θ f g = 0

theorem tsupport_sub_of {f φ : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, g ∉ tsupport f → φ g = 0) :
    tsupport φ ⊆ tsupport f := by
  refine closure_minimal (fun g hg => ?_) (isClosed_tsupport f)
  by_contra hc
  exact hg (h g hc)

theorem suppLoc_RdV (X : Matrix (Fin n) (Fin n) ℂ) : SuppLoc (E := E) (fun f => RdV X f) := by
  intro f g hg
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = 0
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
    have hexp : Continuous (fun Y : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp Y) := by
      letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      exact NormedSpace.exp_continuous
    have h1 : Continuous fun t : ℝ => ((t : ℂ) • X) := by fun_prop
    exact continuous_const.mul (hexp.comp h1)
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => (0 : E) := by
    have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
    have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ (tsupport f)ᶜ := by
      show g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) ∈ (tsupport f)ᶜ
      rw [h0]; exact hg
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hopen.mem_nhds hmem)] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  rw [hev.deriv_eq]
  simp

theorem suppLoc_comp {Θ Θ' : (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E} (h : SuppLoc Θ)
    (h' : SuppLoc Θ') : SuppLoc (fun f => Θ (Θ' f)) := fun f g hg =>
  h _ g fun hg' => hg (tsupport_sub_of (h' f) hg')

theorem suppLoc_EabH (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : SuppLoc (E := E) (EabH H a b) := fun f g hg => by
  show RdV _ f g + Complex.I • RdV _ f g = 0
  have h1 := suppLoc_RdV (E := E) (hpart1 H (Matrix.single a b 1)) f g hg
  have h2 := suppLoc_RdV (E := E) (hpart2 H (Matrix.single a b 1)) f g hg
  simp only at h1 h2
  rw [h1, h2, smul_zero, add_zero]

theorem suppLoc_Top {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SuppLoc (Eop a b)) (u : ℂ) (a b : Fin n) : SuppLoc (Top Eop u a b) := fun f g hg => by
  show (if a = b then u • f g else 0) + Eop a b f g = 0
  rw [hE a b f g hg, image_eq_zero_of_notMem_tsupport hg]
  simp

theorem suppLoc_foldr (l : List ((Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E))
    (h : ∀ T ∈ l, SuppLoc T) : SuppLoc (fun f => l.foldr (fun T φ => T φ) f) := by
  induction l with
  | nil => intro f g hg; exact image_eq_zero_of_notMem_tsupport hg
  | cons T l ih =>
    intro f g hg
    simp only [List.foldr_cons]
    exact suppLoc_comp (h T List.mem_cons_self) (ih fun T' hT' => h T' (List.mem_cons_of_mem _ hT')) f g hg

theorem suppLoc_qminorOp {t : ℕ} {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SuppLoc (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : SuppLoc (qminorOp Eop a b u) := by
  intro f g hg
  unfold qminorOp
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Pi.smul_apply]
  have := suppLoc_foldr (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k))
    (fun T hT => by
      rw [List.mem_ofFn] at hT
      obtain ⟨k, rfl⟩ := hT
      exact suppLoc_Top hE _ _ _) f g hg
  simp only at this
  rw [this, smul_zero]

end Supp

section SuppQ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem suppLoc_chatL {n t : ℕ} {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SuppLoc (Eop a b)) (pos : Fin t → Fin n) (u : ℂ) (a β : Matrix (Fin n) (Fin n) ℂ → Fin t → ℂ) :
    SuppLoc (chatL Eop pos u a β) := fun f g hg => by
  unfold chatL
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [suppLoc_qminorOp hE _ _ u f g hg, smul_zero]

theorem suppLoc_chat2L {n t : ℕ} {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    (hE : ∀ a b, SuppLoc (Eop a b)) (pos : Fin t → Fin n) (u : ℂ)
    (a a' β β' : Matrix (Fin n) (Fin n) ℂ → Fin t → ℂ) : SuppLoc (chat2L Eop pos u a a' β β') := fun f g hg => by
  unfold chat2L
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j _ =>
    Finset.sum_eq_zero fun j' _ => ?_
  split_ifs
  · rw [suppLoc_qminorOp hE _ _ u f g hg, smul_zero]
  · rfl

theorem suppLoc_tL (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) :
    SuppLoc (E := E) (tL k r z z' i Y p q) := by
  have hE : ∀ a b, SuppLoc (E := E) (EH k r a b) := fun a b => suppLoc_EabH _ a b
  intro f g hg
  fin_cases p <;> fin_cases q
  · exact suppLoc_qminorOp hE _ _ _ f g hg
  · show (-(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f)) g = 0
    rw [Pi.neg_apply, suppLoc_chatL hE _ _ _ _ f g hg, neg_zero]
  · show (-(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f)) g = 0
    rw [Pi.neg_apply, suppLoc_chatL hE _ _ _ _ f g hg, neg_zero]
  · show (-(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i)
        (ybv k r z i) (fun _ => xbv k r z' i) f)) g = 0
    rw [Pi.neg_apply, suppLoc_chat2L hE _ _ _ _ _ _ f g hg, neg_zero]

end SuppQ

section SuppOp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def SuppLocOp (Θ : D.Op (Mx k r → (Wq →L[ℂ] Wp))) : Prop := SuppLoc (fun f => D.ap Θ f)

theorem suppLocOp_closed : Formalism.FourierDecayAlt.P.JCx2.mnClosed (SuppLocOp (k := k) (r := r) (Wp := Wp) (Wq := Wq)) where
  zero := fun _ _ _ => rfl
  one := fun f g hg => image_eq_zero_of_notMem_tsupport hg
  add := fun a b ha hb f g hg => by
    show D.ap a f g + D.ap b f g = 0
    have h1 : D.ap a f g = 0 := ha f g hg
    have h2 : D.ap b f g = 0 := hb f g hg
    rw [h1, h2, add_zero]
  mul := fun a b ha hb f g hg => ha (D.ap b f) g fun hg' => hg (tsupport_sub_of (hb f) hg')
  cop := fun c f g hg => by
    show c • f g = 0
    rw [image_eq_zero_of_notMem_tsupport hg, smul_zero]

theorem suppLocOp_rma (z z' : Fin (2 * r + k + 1) → ℂ) (s Y : ℂ) (a b : Fin 2) :
    SuppLocOp (Formalism.FourierDecayAlt.P.JCx2.rma_Qop (Wp := Wp) (Wq := Wq) k r z z' s Y a b) := fun f g hg => by
  show s • tL k r z z' 0 Y a b f g = 0
  rw [suppLoc_tL k r z z' 0 Y a b f g hg, smul_zero]

end SuppOp

section WaveC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem waveJc_wave (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (l : Fin P.r)
    {Wv : Module.End ℂ (RadSp P.k P.r z z' π π')} {s : ℂ} (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) :
    ∀ Ψ ∈ waveJc P z z' π π' D l, Wv Ψ ∈ waveJc P z z' π π' D l := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨hlc, s', ε, G, hε, hN, hG, hv⟩ := hx
    refine Submodule.subset_span ⟨mul_lc hW x hlc, s + s', ε, G, hε, hN, hG, fun y hy => ?_⟩
    rw [hW x y.1 y.2, hv y hy, smul_smul, fsv_add]
  | zero => rw [map_zero]; exact (waveJc P z z' π π' D l).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (waveJc P z z' π π' D l).add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact (waveJc P z z' π π' D l).smul_mem a hx

theorem isWaveJc_jf (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π') (hz : D.z = z)
    (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    IsWaveJc P z z' π π' D l Φ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, ?_⟩
  obtain ⟨ε, hε, hG⟩ := hF.1.2
  refine ⟨0, ε, F, hε, ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hF.1.1 0 m).choose_spec.1), hF.1.1,
    fun g hg hne => by rw [hz, hz']; exact hG g hg hne⟩, hF.2, fun y hy => ?_⟩
  rw [fsv_zero, one_smul]
  exact hΦ y hy

theorem herKc0_le_waveJc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.castSucc = 0) :
    herKc S P z z' π π' L st l0 D 0 ≤ waveJc P z z' π π' D l := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ waveJc P z z' π π' D l := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ =>
      exact fun _ => Submodule.subset_span (isWaveJc_jf P z z' π π' D hD.1 hz hz' hπ hπ' l F hF Φ hΦ)
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
        rw [hVw, hκ, HerD.pr_fst_mul, pr_fst_algebraMap, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
        rfl
      rw [e]
      exact (waveJc P z z' π π' D l').smul_mem κ (waveJc_wave P z z' π π' D l' h1 Φ hv)
    | waveZ w s Wv Wv' a b Φ _ _ _ _ _ =>
      intro h
      exfalso
      have h0 := congrArg Fin.val h
      have h1 := congrArg Fin.val hl
      simp only [Fin.val_last, Fin.val_zero, Fin.val_castSucc] at h0 h1
      have := l.isLt
      omega
  exact key 0 Φ hΦ rfl

theorem rr_picC (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (ε : ℝ) (hε : 0 < ε) (G : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hN : JC.NiceCoef D ε G)
    (hGc : HasCompactSupport G) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : ∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 = resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2)
    (w : List (Letter ℂ S)) (a b : Ix S) :
    ∃ G' : Mx P.k P.r → (Wq →L[ℂ] Wp), JC.NiceCoef D ε G' ∧ HasCompactSupport G' ∧ ∀ y ∈ DomR P.k P.r z z',
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
  have hS := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure (suppLocOp_closed (k := P.k) (r := P.r) (Wp := Wp) (Wq := Wq))
    (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0))
    (fun Y p q => suppLocOp_rma D.z D.z' (M.sgn P l0) Y p q) w
  refine ⟨Formalism.FourierDecayAlt.D.actOp (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w) F' a, ?_, ?_, ?_⟩
  · show JC.NiceCoef D ε (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b'))
    exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' Finset.univ _ fun b' _ => (hR a b').1 (F' b') (hN' b')
  · refine hGc.mono' fun g hg => ?_
    by_contra hgG
    apply hg
    show (∑ b', Formalism.FourierDecayAlt.D.ap (Formalism.FourierDecayAlt.D.RRop (Formalism.FourierDecayAlt.P.JCx2.rma_Qop P.k P.r D.z D.z' (M.sgn P l0)) w a b') (F' b')) g = 0
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun b' _ => hS a b' (F' b') g fun hg' => ?_
    by_cases h : b' = b
    · simp only [F', if_pos h] at hg'; exact hgG hg'
    · simp only [F', if_neg h] at hg'; simp at hg'
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

theorem rr_waveJc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.castSucc = 0) (w : List (Letter ℂ S))
    (hw : WordOK P z z' π π' st l0 w) (a b : Ix S) :
    ∀ Ψ ∈ waveJc P z z' π π' D l, ((RRi L st 0 w) a b).1 Ψ ∈ waveJc P z z' π π' D l := by
  have hRRlc := RRi_lc X μ L st l0 hD 0 w hw.1.2.1
  have hbase : ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ lcSub P.k P.r z z' π π' → ∀ (ε : ℝ), 0 < ε →
      ∀ G, JC.NiceCoef D ε G → HasCompactSupport G → (∀ y ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2) → ∀ c d, ((RRi L st 0 w) c d).1 Φ ∈ waveJc P z z' π π' D l := by
    intro Φ hlc ε hε G hN hGc hΦ c d
    obtain ⟨G', hN', hGc', hpic⟩ := rr_picC P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' ε hε G hN hGc Φ hΦ w c d
    refine Submodule.subset_span ⟨(hRRlc c d).1 Φ hlc, 0, ε, G', hε, hN', hGc', fun y hy => ?_⟩
    rw [fsv_zero, one_smul]
    exact hpic y hy
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem Ψ hx =>
    obtain ⟨hlc, s, ε, G, hε, hN, hGc, hv⟩ := hx
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
        sendsTo (waveJc P z z' π π' D l) Φ := by
      rw [Matrix.mul_apply]
      refine Submodule.sum_mem _ fun d _ => ?_
      rw [Matrix.mul_apply, Finset.sum_mul]
      refine Submodule.sum_mem _ fun c _ => ?_
      obtain ⟨α, hα⟩ := mem_bot_alg (star_entSub (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w) a c)
      obtain ⟨β, hβ⟩ := mem_bot_alg (UUw_mem (A := Pr (RadSp P.k P.r z z' π π')) (𝒜 := ⊥) s w d b)
      rw [hα, hβ]
      exact sendsTo_alg_mul_alg _ Φ (hbase Φ hΦlc ε hε G hN hGc hΦ c d) α β
    have e : ((RRi L st 0 w) a b).1 (Wv Φ) =
        Wv (((star (UUw s w) * RRw (QQi L st 0) w * UUw s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) a b).1 Φ) :=
      congrArg (fun x : Pr (RadSp P.k P.r z z' π π') => x.1 Φ) he
    rw [hΨΦ, e]
    exact waveJc_wave P z z' π π' D l hWv _ hM
  | zero => rw [map_zero]; exact (waveJc P z z' π π' D l).zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact (waveJc P z z' π π' D l).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (waveJc P z z' π π' D l).smul_mem c hx

theorem base0_le_waveJc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.val = 0) :
    base0 S P z z' π π' L st l0 D ≤ waveJc P z z' π π' D l := by
  have hl0 : l.castSucc = (0 : Fin (P.r + 1)) := Fin.ext (by simp [hl])
  have hK := herKc0_le_waveJc (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0
  refine sup_le hK (Submodule.span_le.mpr ?_)
  rintro Φ ⟨w, hw, a, b, Ψ, hΨ, rfl⟩
  exact rr_waveJc (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl0 w hw a b Ψ (hK hΨ)

end WaveC

end Formalism.FourierDecayAlt.P.CutSE
