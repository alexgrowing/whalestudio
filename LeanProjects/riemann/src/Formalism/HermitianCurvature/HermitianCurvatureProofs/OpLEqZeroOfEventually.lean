import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepFormCptAllOfStepFormAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFOfCls
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferWordEntriesMem

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Loc

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def VanOut (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (K : Set (Mx k r)) : Prop :=
  ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0

def LCptAt (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  ∃ U : Set (Fin r → ℂ), IsOpen U ∧ c ∈ U ∧ ∃ K : Set (Mx k r), IsCompact K ∧ K ⊆ {g | 0 < GGl k r z z' g} ∧
    ∀ c' ∈ U, VanOut Φ c' K

variable (k r z z' π π') in

def lcSub : Submodule ℂ (RadSp k r z z' π π') where
  carrier := {Φ | ∀ c ∈ OmX r, LCptAt Φ c}
  zero_mem' := fun c _ => ⟨Set.univ, isOpen_univ, trivial, ∅, isCompact_empty, Set.empty_subset _,
    fun _ _ _ _ _ => rfl⟩
  add_mem' := by
    intro Φ Ψ hΦ hΨ c hc
    obtain ⟨U1, hU1, hc1, K1, h1c, h1G, h10⟩ := hΦ c hc
    obtain ⟨U2, hU2, hc2, K2, h2c, h2G, h20⟩ := hΨ c hc
    refine ⟨U1 ∩ U2, hU1.inter hU2, ⟨hc1, hc2⟩, K1 ∪ K2, h1c.union h2c, Set.union_subset h1G h2G,
      fun c' hc' g hg hgK => ?_⟩
    show (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g + (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g = 0
    rw [h10 c' hc'.1 g hg (fun h => hgK (Or.inl h)), h20 c' hc'.2 g hg (fun h => hgK (Or.inr h)), add_zero]
  smul_mem' := by
    intro a Φ hΦ c hc
    obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
    refine ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' g hg hgK => ?_⟩
    show a • (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g = 0
    rw [hK0 c' hc' g hg hgK, smul_zero]

theorem lcSub_le_cptSub : lcSub k r z z' π π' ≤ cptSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨K, hKc, hKG, hK0 c hcU⟩

theorem fn_van (X : ActualOps k r z z' π π') (j : Fin 6) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (K : Set (Mx k r)) (h : VanOut Φ c K) : VanOut (X.fn j Φ) c K := by
  intro g hg hgK
  by_cases hx : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · rw [X.fn_apply j Φ (c, g) hx, h g hg hgK, smul_zero]
  · exact (X.fn j Φ).2.1 (c, g) hx

theorem mul_van {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (K : Set (Mx k r)) (h : VanOut Φ c K) : VanOut (W Φ) c K := by
  intro g hg hgK
  rw [hW Φ c g, h g hg hgK, smul_zero]

theorem t_van (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ)
    (K : Set (Mx k r)) (hKc : IsCompact K) (h : VanOut Φ c K) : VanOut (X.t Y a b Φ) c K := by
  intro g hg hgK
  by_cases hd : (c, g) ∈ DomR k r z z'
  · have e := X.t_apply Y a b Φ (c, g) hd
    simp only at e
    rw [e]
    set D : Set (Mx k r) := {g | 0 < GGl k r z z' g} \ K with hDdef
    have hDo : IsOpen D := (isOpen_lt continuous_const (P.Qx5.GGl_continuous k r z z')).sdiff hKc.isClosed
    have hDG : D ⊆ {g | 0 < GGl k r z z' g} := Set.sdiff_subset
    have hgD : g ∈ Glev k r (Fin.last r) ∩ D := ⟨hg, hd.2.2, hgK⟩
    have hS1 := smoothLev_slice Φ c hd.1 D hDG
    have hS0 : SmoothLev k r (Fin.last r) D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) := by
      intro g₀ _
      exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
    have hL := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) (fun _ => 0) 1 hDo hS1 hS0 g hgD
    have hL0 := Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' (Fin.last r) D Y a b
      (fun _ => (0 : Wq →L[ℂ] Wp)) (fun _ => 0) 1 hDo hS0 hS0 g hgD
    have h0 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
      have h := hL0.1
      simp only [smul_zero, add_zero, one_smul] at h
      have h2 : tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
          tL k r z z' (Fin.last r) Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g + 0 := by
        rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    have hloc := hL.2 (fun x hx => h x hx.1 hx.2.2)
    rw [show (Φ : Fn k r (Wq →L[ℂ] Wp)) c = fun g => (Φ : Fn k r (Wq →L[ℂ] Wp)) c g from rfl, hloc, h0]
  · exact radSp_zero_off (X.t Y a b Φ) (x := (c, g)) hd

theorem opL_eq_zero_of_eventually {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (i : Fin 6)
    (f : (Fin r → ℂ) → E) (c : Fin r → ℂ) (hf : f =ᶠ[𝓝 c] fun _ => 0) : opL l i f c = 0 := by
  have h0 : f c = 0 := hf.self_of_nhds
  have hd : fderiv ℝ f c = 0 := by
    rw [hf.fderiv_eq]
    exact fderiv_const_apply 0
  fin_cases i <;> simp [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, h0, hd]

theorem op_van (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π')
    (U : Set (Fin r → ℂ)) (hU : IsOpen U) (K : Set (Mx k r)) (h : ∀ c' ∈ U, VanOut Φ c' K) :
    ∀ c ∈ U, VanOut (X.op l i Φ) c K := by
  intro c hc g hg hgK
  rw [X.op_apply l i Φ]
  show opL l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c = 0
  apply opL_eq_zero_of_eventually
  filter_upwards [hU.mem_nhds hc] with c' hc'
  exact h c' hc' g hg hgK

theorem fn_lc (X : ActualOps k r z z' π π') (j : Fin 6) :
    ∀ Φ ∈ lcSub k r z z' π π', X.fn j Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' => fn_van X j Φ c' K (hK0 c' hc')⟩

theorem t_lc (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    ∀ Φ ∈ lcSub k r z z' π π', X.t Y a b Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' => t_van X Y a b Φ c' K hKc (hK0 c' hc')⟩

theorem mul_lc {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m) :
    ∀ Φ ∈ lcSub k r z z' π π', W Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, fun c' hc' => mul_van hW Φ c' K (hK0 c' hc')⟩

theorem op_lc (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) :
    ∀ Φ ∈ lcSub k r z z' π π', X.op l i Φ ∈ lcSub k r z z' π π' := by
  intro Φ hΦ c hc
  obtain ⟨U, hU, hcU, K, hKc, hKG, hK0⟩ := hΦ c hc
  exact ⟨U, hU, hcU, K, hKc, hKG, op_van X l i Φ U hU K hK0⟩

end Loc

section Alg

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem neg_lc {T : Module.End ℂ (RadSp k r z z' π π')} (hT : ∀ Φ ∈ lcSub k r z z' π π', T Φ ∈ lcSub k r z z' π π') :
    ∀ Φ ∈ lcSub k r z z' π π', (-T) Φ ∈ lcSub k r z z' π π' := fun Φ hΦ => by
  rw [LinearMap.neg_apply]
  exact (lcSub k r z z' π π').neg_mem (hT Φ hΦ)

theorem mkPair_mem_preservingAlgebra {T T' : Module.End ℂ (RadSp k r z z' π π')}
    (hT : ∀ Φ ∈ lcSub k r z z' π π', T Φ ∈ lcSub k r z z' π π')
    (hT' : ∀ Φ ∈ lcSub k r z z' π π', T' Φ ∈ lcSub k r z z' π π') :
    mkP T T' ∈ presAlg (lcSub k r z z' π π') := ⟨fun Φ hΦ => hT Φ hΦ, fun Φ hΦ => hT' Φ hΦ⟩

theorem UUiw_mem {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUiw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUiw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Uinv (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Uinv, 𝒜.one_mem, 𝒜.zero_mem, 𝒜.algebraMap_mem]

end Alg

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
  {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ} {D : B.RealPlaceData P.k P.r Wp Wq}

theorem herGenC_lc (X : ActualOps P.k P.r z z' π π') (hAL : IsActualLevel X L)
    (hJ : ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π'), JFOKCpt P z z' F →
      IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π')
    {i : Fin (P.r + 1)} {Φ : RadSp P.k P.r z z' π π'} (h : HerGenC S P z z' π π' L st l0 D i Φ) :
    Φ ∈ lcSub P.k P.r z z' π π' := by
  have hsite : ∀ l : Fin P.r, (site L l).p ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      (site L l).c ∈ presAlg (lcSub P.k P.r z z' π π') ∧ (site L l).ci ∈ presAlg (lcSub P.k P.r z z' π π') := by
    intro l
    refine ⟨?_, ?_, ?_⟩
    · show L.p l ∈ _
      rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
    · show L.c l ∈ _
      rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
    · show L.ci l ∈ _
      rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)
  induction h with
  | jf F Φ hF hΦ => exact hJ F Φ hF hΦ
  | slice l w a b Φ _ _ ih =>
    obtain ⟨hp, hc, hci⟩ := hsite l
    exact (Formalism.FourierDecayAlt.P5.HerA.bT_mem (site L l) hp hc hci w a b).1 Φ ih
  | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
    have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
        entSub (presAlg (lcSub P.k P.r z z' π π')) :=
      (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (mkPair_mem_preservingAlgebra (mul_lc h1) (mul_lc h2))) (UUiw_mem s w)
    exact (hm a b).1 Φ ih
  | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
    have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
        entSub (presAlg (lcSub P.k P.r z z' π π')) :=
      (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (mkPair_mem_preservingAlgebra (mul_lc h1) (mul_lc h2))) (UUiw_mem s w)
    exact (hm a b).1 Φ ih

theorem herKc_le_lc (X : ActualOps P.k P.r z z' π π') (hAL : IsActualLevel X L)
    (hJ : ∀ (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (Φ : RadSp P.k P.r z z' π π'), JFOKCpt P z z' F →
      IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π') (i : Fin (P.r + 1)) :
    herKc S P z z' π π' L st l0 D i ≤ lcSub P.k P.r z z' π π' := Submodule.span_le.2 fun Φ h => herGenC_lc X hAL hJ h

end Classes

def JFCptLocAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (D : B.RealPlaceData P.k P.r Wp Wq) (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (Φ : RadSp P.k P.r z z' π π'),
    IsPlace P z z' π π' → D.z = z → D.z' = z' → D.π = π → D.π' = π' → JFOKCpt P z z' F →
    IsRadJF P z z' π π' D F Φ → Φ ∈ lcSub P.k P.r z z' π π'

theorem herCptTopAll_of_jf (hJ : JFCptLocAll) : HerCptTopAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ'
  refine (herKc_le_lc X hD.2.2.1
    (fun F Φ hF hR => hJ Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hR) (Fin.last P.r)).trans ?_
  exact lcSub_le_cptSub

theorem thmPActualCpt_of_jf (hJ : JFCptLocAll) (hSF : StepFormCptAll) : ThmPActualCpt := thmPActualCpt_of_parts (herCptTopAll_of_jf hJ) hSF

end Formalism.FourierDecayAlt.P5.HerC
