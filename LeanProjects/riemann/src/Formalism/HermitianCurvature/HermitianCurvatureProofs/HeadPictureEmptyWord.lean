import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceInductionLevel

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
