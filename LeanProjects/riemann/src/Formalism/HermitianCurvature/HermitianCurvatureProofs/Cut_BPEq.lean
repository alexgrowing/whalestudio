import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFinal

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ptBound_main (hA : P5.ThmPActual) (Cb : ℝ) : ∃ C₂ c₃ Cc Cc' : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (q : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P q.l0 q.T.base Cb q.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      TBBx5.WaveGrid q nn Y Λ K N → TBBx5.LiftGrid q nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound q nn (apx (D.cutF q.T.base χ F ε) n) Y K N) →
      (∀ w, TBB.AdmW P q.l0 Y w → w.length ≤ N → DomCut q χ F w) →
      LimBd q nn F Y N → TBB.PtBound q F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_dec_all hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  obtain ⟨Cc', hE⟩ := limE_of_limEvT hA Cb
  refine ⟨C₂, c₃, Cc, Cc', hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth1 hth2 hth3 hWG hLG hI5 hDom hBd
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCc Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA hth2)
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA hth3 (limEvT_of_dom q hχ hF Y N hDom) hBd)
    (lemB_one q F)

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem ttp_eq (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') (hz : q.T.base.z = p.T.base.z)
    (hz' : q.T.base.z' = p.T.base.z') : TTp q = TTp p := by
  unfold Formalism.FourierDecayAlt.TBB.TTp
  rw [hz, hz']
  rfl

theorem isBoundedBilinearMap_compSh :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq' →L[ℂ] Wq) => q.1.comp q.2) where
  add_left x₁ x₂ y := ContinuousLinearMap.add_comp x₁ x₂ y
  smul_left c x y := by ext v; simp
  add_right x y₁ y₂ := ContinuousLinearMap.comp_add x y₁ y₂
  smul_right c x y := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
    exact ContinuousLinearMap.map_smul_of_tower x c (y v)
  bound := ⟨1, one_pos, fun x y => by simpa using ContinuousLinearMap.opNorm_comp_le x y⟩

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_compSh {k r : ℕ} {f : B.Mat k r → (Wq →L[ℂ] Wp)} {A : B.Mat k r → (Wq' →L[ℂ] Wq)}
    (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (f2 g), hU1.inter hU2, ⟨hg1, hg2⟩, ?_,
    fun g hg hgv => by
      show (f g).comp (A g) = (f1 g).comp (f2 g)
      rw [he1 g hg.1 hgv, he2 g hg.2 hgv]⟩
  have hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (f1 g, f2 g)) (U1 ∩ U2) := by
    first
    | exact (hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right)
    | exact (hc1.mono Set.inter_subset_left).prod (hc2.mono Set.inter_subset_right)
  exact isBoundedBilinearMap_compSh.contDiff.comp_contDiffOn hp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ckOn_fpmSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hA : B.CkOn ⊤ (B.GV P.k P.r) A) : B.CkOn ⊤ (B.GV P.k P.r) (fpmSh q f A p₀) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun g : B.Mat P.k P.r => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf q.T.base.z q.T.base.z').pow p₀)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hc (ckOn_compSh hf hA)

end sh

def PolyOp {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (d : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∃ (n : ℕ) (c : Fin n → B.Mat k r → ℂ) (L : Fin n → (Wq' →L[ℂ] Wq)),
    (∀ i, U.IsPolyDeg d (c i)) ∧ ∀ g, A g = ∑ i, c i g • L i

def FpmShDecay : Prop :=
  ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ) (d p₀ : ℕ),
    (∀ m : ℕ, B.InCC A₀ m f) → PolyOp d A →
    ∀ m : ℕ, B.InCC (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m (fpmSh q f A p₀)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
      [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
      (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
      (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₁ : ℝ) (n₀ p₀ : ℕ)
      (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
      pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      (∀ m : ℕ, B.InCC A₁ m (fpmSh pp f Ap p₀)) → (∀ m : ℕ, B.InCC A₁ m (fpmSh pm f Am p₀)) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₁ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N →
      TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) →
      (∀ w, TBB.AdmW (shP P up up') pp.l0 Yp w → w.length ≤ N → DomCut pp χ (fpmSh pp f Ap p₀) w) →
      (∀ w, TBB.AdmW (shP P um um') pm.l0 Ym w → w.length ≤ N → DomCut pm χ (fpmSh pm f Am p₀) w) →
      LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, c₃, Cc, Cc', hC₂, hPt⟩ := ptBound_main hA Cb
  obtain ⟨C₄, hC₄⟩ := thmBpOfPartsSh C₃ CΛ C₀ C₂ 0 hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₁ n₀ p₀ χ nnp nnm
    Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hAp hAm hdp hdm hth1 hth2
    hth3 hAms hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := hN P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀ hzp hzp' hzm hzm' hAms
  have hReg := Formalism.FourierDecayAlt.P.regularity_at_place p f b C₃ (2 * p₀ + n₀) (by linarith) hexp
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ A₁ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf hAp) hdp hth1 hth2 hth3 hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ A₁ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf hAm) hdm hth1 hth2 hth3 hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ 1 n₀ p₀ hb hΛ hΛb one_pos (by simp) hT hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

end

end Formalism.FourierDecayAlt.P.CutBPEq
