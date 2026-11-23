import Formalism.HermitianCurvature.HermitianCurvatureProofs.DetCornerMatrixLevelZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CastVMulVecLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exAt (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ := by
  classical
  have hV := grpInt_at_dframe p hLev Ψ x hx hγG hζ hγF
  have hPl : Q.IsPlace (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨P.r, by omega⟩ p.hP
  have hn : P.r + (P.r - P.r) = P.r := by omega
  have hz : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have hν : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.castV_mulVec_lift hn, hLev.1, hLev.2.1]
  have hπ : (p.T.bs P.r).π = fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y)) :=
    funext fun y => p.T.π_lev P.r le_rfl y
  have hcap : ∀ (Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (w : ℂ) (v : Wp),
      Q.capRep P.k (P.r - P.r) (p.T.bs P.r).π Bs w v =
        Q.capRep P.k P.r p.T.base.π (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) w v := by
    intro Bs w v
    rw [Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.capRep_lift_cast hn, hπ]
  have hfr : ∀ Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ,
      Q.IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z, m₀r *ᵥ ν'r] Bs →
        Q.IsFrameOf P.k P.r [p.T.base.z, p.m₀ *ᵥ p.ν'] (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) := by
    intro Bs hB
    have h := Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.frame_lift_cast hn _ Bs hB
    simpa only [List.map_cons, List.map_nil, hz, hν] using h
  let TP' : Top.TypeProj (JC.parLev P P.r) (p.T.bs P.r).π (p.T.bs P.r).z (m₀r *ᵥ ν'r) :=
    { E := p.TP.E
      idem := p.TP.idem
      orth := p.TP.orth
      selfAdj := p.TP.selfAdj
      eigen := fun Bs hB ρ w v => (hcap Bs w _).trans (p.TP.eigen _ (hfr Bs hB) ρ w v)
      full := fun Bs hB ρ v h => p.TP.full _ (hfr Bs hB) ρ v fun w => (hcap Bs w v).symm.trans (h w) }
  exact types_of_grpInt (JC.parLev P P.r) (p.T.bs P.r) ν'r m₀r TP' hPl hLev.2.2 _ hV

def HeadWeightAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_types_at_of_weight : PBI.HeadWeightAt → PBI.HeadTypesAt := by
  intro hW Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF
  exact ⟨fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF,
    hW Wp Wq P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF⟩

end Formalism.FourierDecayAlt.P
