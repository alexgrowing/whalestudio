import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTypesAtOfWeight
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialHeadTypes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

def Exh : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V F₂ (h ++ [(1, ζ)])) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

def HeadVecOfParts : Prop := HighestUnipotentIntegral → Exh → HeadVec

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_vector_of_parts : PBI.HeadVecOfParts := by
  intro hU5 hExh Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF h hh Φ hΦ e
  obtain ⟨F₂, hF₂, hV, hJ⟩ := hExh Wp Wq P p F w X μ L st Cb hD hdd hF hcut e h hh
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hr : P.r - P.r = 0 := by omega
  have hGx : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hGx
    nlinarith [mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos]
  have hZ : Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ = D.ptMatN [(1, ζ)] (P.r - P.r + 1) := by
    ext a b
    have ha : a = Fin.last _ := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
    have hb : b = Fin.last _ := Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
    subst ha hb
    rw [← PBI.zetaL_eq_zhat, hζ]
    simp [D.ptMatN, D.ptEntry, hr]
  have hγGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ := by
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx
  show p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = _
  rw [hV, hU5 Wp Wq P p F₂ h ζ hh ν'r m₀r hF₂ hζ0 hLev.1 hLev.2.1,
    PBM.vector_level_zero_eq_jacquet hr (p.T.bs P.r) ν'r m₀r hLev.2.2 _ ζ (by linarith) γ₀ hγG hZ hγF]
  exact hJ Φ hΦ x.1 γ₀ hγG hγGG

end Formalism.FourierDecayAlt.P
