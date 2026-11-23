import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure ShiftAtR {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
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
  polyP : PolyOp (n₀ * (P.r + 1)) Ap
  polyM : PolyOp (n₀ * (P.r + 1)) Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAtR.iNp ShiftAtR.iIp ShiftAtR.iFp ShiftAtR.iNm ShiftAtR.iIm ShiftAtR.iFm

theorem thmBpAt_eq_of_shiftR (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃)
    (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAtR p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ) →
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
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - ((n₀ * (P.r + 1) : ℕ) : ℝ)) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀
    hp₀ S.hzp S.hzp' S.hzm S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP)
    (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ (n₀ * (P.r + 1)) p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm

section pieces

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

def SwapTie (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq') : Prop :=
  q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧
    q.T.base.μW = p.T.base.μW ∧ q.T.base.μN = p.T.base.μN ∧ q.T.base.μW' = p.T.base.μW' ∧
    q.ν' = p.ν' ∧ q.m₀ = p.m₀

open Classical in

def ptRep (p : KB.Pl P Wp Wq) (γ : C.LPt) : B.Mat P.k P.r :=
  if h : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g then h.choose else 1

end pieces

def WigEquiv {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (π' : B.Mat k r → (Wq →L[ℂ] Wq))
    (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, A (n * g * n') = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h ∈ UWset k r z, A (h * g) = A g) ∧
  (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ h' ∈ UWset k r z', A (g * h') = (π' h'⁻¹).comp ((A g).comp (π'' h')))

def WigUpper {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] (z z' : Fin (2 * r + k + 1) → ℂ) (n₀ : ℕ) (A : B.Mat k r → (Wq' →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, ‖A g‖ ^ 2 ≤ (Gf k r z z' g / Tz k r z') ^ n₀

def WigLower {k r : ℕ} {Wq Wqp Wqm : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wq] [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (z z' : Fin (2 * r + k + 1) → ℂ) (b : ℝ) (n₀ : ℕ)
    (Ap : B.Mat k r → (Wqp →L[ℂ] Wq)) (Am : B.Mat k r → (Wqm →L[ℂ] Wq)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ v : Wq,
    ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (Tz k r z' / Gf k r z z' g) ^ n₀ *
      (‖(ContinuousLinearMap.adjoint (Ap g)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (Am g)) v‖ ^ 2)

def CellIdSh : Prop :=
  ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq Wq' : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
    (u u' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (q : KB.Pl (shP P u u') Wp Wq')
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (A₀ : ℝ),
    SwapTie p q → WigEquiv p.T.base.z p.T.base.z' p.T.base.π' q.T.base.π' A →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < Gp p γ →
      q.V (fun g => (f g).comp (A g)) γ = (p.V f γ).comp (A (ptRep p γ))

theorem ptRep_spec {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) {γ : C.LPt} (hγ : D.IsLocPt γ (P.r + 1)) (hG : 0 < Gp p γ) :
    ptRep p γ ∈ B.GV P.k P.r ∧ Gf P.k P.r p.T.base.z p.T.base.z' (ptRep p γ) = Gp p γ := by
  have hex : ∃ g ∈ B.GV P.k P.r, Zhat P.k P.r p.T.base.z p.T.base.z' g = D.ptMatN γ (P.r + 1) ∧
      D.IsDFrame p.T.base p.ν' p.m₀ g :=
    Formalism.FourierDecayAlt.P.Dx2.dFrameExists P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ p.hF hγ hG
  have hrep : ptRep p γ = hex.choose := by
    unfold ptRep
    rw [dif_pos hex]
  obtain ⟨hmem, hz, _⟩ := hex.choose_spec
  refine ⟨by rw [hrep]; exact hmem, ?_⟩
  rw [hrep, Formalism.FourierDecayAlt.P.TBBx2.Gf_of_Zhat _ _ _ γ hz]
  rfl

theorem shiftAtR_of_parts (hC : CellIdSh) : ∃ c₃ : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
    [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (A₀ : ℝ)
    (up up' um um' : ℕ → ℝ) (pp : KB.Pl (shP P up up') Wp Wqp) (pm : KB.Pl (shP P um um') Wp Wqm)
    (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)),
    SwapTie p pp → SwapTie p pm →
    WigEquiv p.T.base.z p.T.base.z' p.T.base.π' pp.T.base.π' Ap →
    WigEquiv p.T.base.z p.T.base.z' p.T.base.π' pm.T.base.π' Am →
    PolyOp (n₀ * (P.r + 1)) Ap → PolyOp (n₀ * (P.r + 1)) Am →
    WigUpper p.T.base.z p.T.base.z' n₀ Ap → WigUpper p.T.base.z p.T.base.z' n₀ Am →
    WigLower p.T.base.z p.T.base.z' b n₀ Ap Am →
    c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₀ → B.InCC A₀ 1 f →
    ∃ S : ShiftAtR p f b n₀, S.up = up ∧ S.up' = up' ∧ S.um = um ∧ S.um' = um' ∧ S.pp.l0 = pp.l0 ∧
      S.pm.l0 = pm.l0 := by
  obtain ⟨c₃, hC⟩ := hC
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ p f b n₀ A₀ up up' um um' pp pm Ap Am htp htm hep hem hpp hpm
    hup hum hlo hA₀ hf
  refine ⟨⟨up, up', um, um', Wqp, Wqm, pp, pm, Ap, Am, fun γ => Ap (ptRep p γ), fun γ => Am (ptRep p γ),
    htp.1, htp.2.1, htm.1, htm.2.1, hpp, hpm, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun γ hγ hG => hC P Wp Wq Wqp up up' p pp f Ap A₀ htp hep hA₀ hf γ hγ hG,
    fun γ hγ hG => hC P Wp Wq Wqm um um' p pm f Am A₀ htm hem hA₀ hf γ hγ hG, ?_, ?_, ?_⟩
  · intro γ hγ hG v
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := hlo _ hmem (by rw [hGf]; exact hG) v
    rw [hGf] at h
    exact h
  · intro γ hγ hG
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := hup _ hmem
    rw [hGf] at h
    exact h
  · intro γ hγ hG
    obtain ⟨hmem, hGf⟩ := ptRep_spec p hγ hG
    have h := hum _ hmem
    rw [hGf] at h
    exact h

end

end Formalism.FourierDecayAlt.P.CutBPEq
