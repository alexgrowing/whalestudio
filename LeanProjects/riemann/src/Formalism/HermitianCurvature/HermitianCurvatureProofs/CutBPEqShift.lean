import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqDecay

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem ckOn_of_polyOp {d : ℕ} {A : B.Mat k r → (Wq' →L[ℂ] Wq)} (hA : PolyOp d A) : B.CkOn ⊤ (B.GV k r) A := by
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  have hconst : ∀ i, B.CkOn ⊤ (B.GV k r) (fun _ : B.Mat k r => L i) := fun i _ _ =>
    ⟨Set.univ, fun _ => L i, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hterm : ∀ i, B.CkOn ⊤ (B.GV k r) (fun g => c i g • L i) := fun i =>
    (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wq) (Wq := Wq') (hc i)).1 _ (hconst i)
  have hsum : ∀ s : Finset (Fin n), B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, c i g • L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩
    | insert a s ha ih =>
      have e : (fun g => ∑ i ∈ insert a s, c i g • L i) = (fun g => c a g • L a) + fun g => ∑ i ∈ s, c i g • L i := by
        funext g; simp [Finset.sum_insert ha]
      rw [e]; exact Formalism.FourierDecayAlt.P.B4.ckOn_add (hterm a) ih
  have e : A = fun g => ∑ i, c i g • L i := funext hAe
  rw [e]; exact hsum Finset.univ

end poly

structure ShiftAt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp n₀ Ap
  polyM : PolyOp n₀ Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAt.iNp ShiftAt.iIp ShiftAt.iFp ShiftAt.iNm ShiftAt.iIm ShiftAt.iFm

theorem thmBpAt_eq_of_shift (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃)
    (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAt p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pp nnp (apx (D.cutF S.pp.T.base χ (fpmSh S.pp f S.Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pm nnm (apx (D.cutF S.pm.T.base χ (fpmSh S.pm f S.Am p₀) ε) n) Ym K N) →
      (∀ w, TBB.AdmW (shP P S.up S.up') S.pp.l0 Yp w → w.length ≤ N → DomCut S.pp χ (fpmSh S.pp f S.Ap p₀) w) →
      (∀ w, TBB.AdmW (shP P S.um S.um') S.pm.l0 Ym w → w.length ≤ N → DomCut S.pm χ (fpmSh S.pm f S.Am p₀) w) →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ := thmBpAt_eq hA hN Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  exact h P Wp Wq S.Wqp S.Wqm S.up S.up' S.um S.um' p S.pp S.pm f S.Ap S.Am S.ApPt S.AmPt b Λ
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ S.hzp S.hzp' S.hzm
    S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP) (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ n₀ p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ n₀ p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq
