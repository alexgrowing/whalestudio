import Formalism.HermitianCurvature.HermitianCurvatureProofs.DframeCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormAnisotropicPart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentLevelZeroEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section lev

variable {k : ℕ}

theorem det_corner_matrix_level_zero {r' : ℕ} (hr : r' = 0) (z z' : Fin (2 * r' + k + 1) → ℂ) (g : B.Mat k r') :
    (Zhat k r' z z' g).det = Q.zetaL k r' z z' (Fin.last r') g := by
  subst hr
  exact (Matrix.det_fin_one _).trans rfl

theorem castV_herm {a b : ℕ} (h : a = b) (v w : Fin (2 * a + k + 1) → ℂ) :
    herm (Hpk k b) (D.castV h v) (D.castV h w) = herm (Hpk k a) v w := by
  subst h
  rfl

theorem capRep_cast {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {a b m : ℕ} (h : a = b)
    (π : Q.Mx k b → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * a + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    Q.capRep k a (fun y => π (D.castM h y)) Bs w v = Q.capRep k b π (fun c => D.castV h (Bs c)) w v := by
  subst h
  rfl

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem grpInt_at_dframe (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    GrpInt (p.T.bs P.r) ν'r m₀r ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) := by
  have hG : 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' := hx.2.2
  have hT := mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos
  have hdet : (Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀).det ≠ 0 := by
    rw [det_corner_matrix_level_zero (Nat.sub_self P.r), hζ]
    intro h0
    rw [h0, map_zero] at hG
    linarith
  have hdom : ((x.1, γ₀) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r) ∈
      Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := by
    refine ⟨hx.1, ⟨hγG, fun a _ => ?_⟩, ?_⟩
    · exfalso
      have ha := a.isLt
      revert ha
      show ¬ (a.val < P.r - P.r)
      omega
    · show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
        Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
      rw [hζ]
      exact hG
  obtain ⟨-, -, he⟩ := Ψ.2
  intro hB hhB hBν
  have e := he (x.1, γ₀) hdom _ (Formalism.FourierDecayAlt.P.Topx1.vecw_conj_mem _ hLev.2.2 hhB) _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hhB)
  try dsimp only at e
  have hc := Formalism.FourierDecayAlt.P.PBI.dframe_commute _ (Nat.sub_self P.r) hLev.2.2 hγG hγF hdet hhB hBν
  exact e.symm.trans (congrArg (fun g => (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 g) hc)

end place

end Formalism.FourierDecayAlt.P.PBI
