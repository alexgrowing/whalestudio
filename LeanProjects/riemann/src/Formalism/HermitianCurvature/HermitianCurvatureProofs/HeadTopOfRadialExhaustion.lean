import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

def ExhPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    KB.IsTopLift2 P p.l0 p.T.base L₀ st₀ p.Θ →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧ KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ Φ₁ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ₁ F₁ →
        Top.IsRadOf P p.T.base
          (P5.act ((Fr.ofWord L₀ st₀ (D.positionted w)).F * P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e) F₂) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem exhaustion_of_radial_form : PBI.ExhPic → PBI.Exh := by
  intro hPic Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut e h hh
  obtain ⟨X₀, μ₀, L₀, st₀, hD₀, hTL⟩ := p.hΘ
  obtain ⟨F₁, F₂, hF₁, hF₂, hloc, hpic, hii⟩ :=
    hPic Wp Wq P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  obtain ⟨F', hF', hagree, hVeq⟩ := theta_compact_support Wp Wq P p F₁ w e Cb hdd hF₁ hcut
  refine ⟨F₂, hF₂, fun ζ => ?_, hii⟩
  obtain ⟨Φ₁, hΦ₁⟩ := PBN.radExists p hF₁
  have hΘpic := hTL w hcut F₁ hF₁ Φ₁ hΦ₁ e
  have hF'pic := PBN.isRadOf_congr p.T.base hΘpic hagree
  rw [hloc ζ, hVeq]
  exact PBN.vecV_eq_of_rad density_constant p hF' hF₂ hF'pic (hpic Φ₁ hΦ₁) _

theorem head_top_of_radial_exhaustion (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) (hW : PBI.HeadWeightAt) : KB.HeadTop :=
  head_top_of_parts hU5 (exhaustion_of_radial_form hPic) hW

end Formalism.FourierDecayAlt.P
