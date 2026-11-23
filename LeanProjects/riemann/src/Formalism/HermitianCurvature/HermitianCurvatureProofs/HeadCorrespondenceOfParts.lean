import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

namespace Formalism.FourierDecayAlt.P.PBI

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

private theorem det_ptMatN_append_eq_mul (h : C.LPt) (ζ : ℂ) :
    (D.ptMatN (h ++ [(1, ζ)]) (D.ptSize h + 1)).det = ζ * (D.ptMatN h (D.ptSize h)).det := by
  rw [Matrix.det_succ_row _ (Fin.last _), Finset.sum_eq_single (Fin.last _)]
  · have e1 : (D.ptMatN (h ++ [(1, ζ)]) (D.ptSize h + 1)) (Fin.last _) (Fin.last _) = ζ := by
      simp only [D.ptMatN, Fin.val_last]
      exact PBD.ptEntry_app_last ζ h
    have e2 : (D.ptMatN (h ++ [(1, ζ)]) (D.ptSize h + 1)).submatrix (Fin.last _).succAbove
        (Fin.last _).succAbove = D.ptMatN h (D.ptSize h) := by
      ext a b
      simp only [Matrix.submatrix_apply, Fin.succAbove_last, D.ptMatN, Fin.coe_castSucc]
      exact PBD.ptEntry_app_lt ζ h a b a.2 b.2
    have e4 : ((-1 : ℂ)) ^ ((Fin.last (D.ptSize h) : ℕ) + (Fin.last (D.ptSize h) : ℕ)) = 1 := by
      rw [Fin.val_last, ← two_mul, pow_mul]
      norm_num
    rw [e1, e2, e4, one_mul]
  · intro j _ hj
    have hj' : (j : ℕ) < D.ptSize h := by
      have h1 := j.2
      have h2 : (j : ℕ) ≠ D.ptSize h := fun e => hj (Fin.ext (by simp [e]))
      omega
    have e3 : (D.ptMatN (h ++ [(1, ζ)]) (D.ptSize h + 1)) (Fin.last _) j = 0 := by
      simp only [D.ptMatN, Fin.val_last]
      exact PBD.ptEntry_app_row ζ h j hj'
    rw [e3]
    simp
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem det_ptMatN_ne (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) : (D.ptMatN h n).det ≠ 0 := by
  obtain ⟨hb, hs⟩ := hh
  subst hs
  have hM : D.ptMatN h (D.ptSize h) = U.hMat (D.ptPerm h) (D.ptDiag h) :=
    (ptPerm_spec h _ ⟨hb, rfl⟩).2.2
  rw [hM, U.hMat, Matrix.det_mul, Matrix.det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun a _ => Dx1.Rel.scal_ne h hb a a.2)

  have hw : U.wP (D.ptPerm h) = (D.ptPerm h).permMatrix ℂ := by
    ext a b
    simp [U.wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  rw [hw, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (D.ptPerm h)) with e | e <;> simp [e]

theorem wPt_app (TT : ℝ) (ζ : ℂ) (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) :
    Top.wPt TT n (h ++ [(1, ζ)]) = Complex.normSq ζ / (Complex.normSq ζ - TT) := by
  have hs : D.ptSize h = n := hh.2
  have hd : (D.ptMatN h n).det ≠ 0 := det_ptMatN_ne h n hh
  have hn : D.ptMatN (h ++ [(1, ζ)]) n = D.ptMatN h n := by
    ext a b
    subst hs
    exact PBD.ptEntry_app_lt ζ h a b a.2 b.2
  have hn1 : (D.ptMatN (h ++ [(1, ζ)]) (n + 1)).det = ζ * (D.ptMatN h n).det := by
    subst hs
    exact det_ptMatN_append_eq_mul h ζ
  have hq : Complex.normSq (D.ptMatN h n).det ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  simp only [Top.wPt, D.ptG, hn, hn1, Complex.normSq_mul]
  rw [show Complex.normSq ζ * Complex.normSq (D.ptMatN h n).det - TT * Complex.normSq (D.ptMatN h n).det =
      (Complex.normSq ζ - TT) * Complex.normSq (D.ptMatN h n).det by ring]
  exact mul_div_mul_right _ _ hq

theorem dH_app (P : M.Par) (l0 : ℕ) (TT : ℝ) (w : List C.Letter) (ζ : ℂ) (h h' : C.LPt)
    (hh : D.IsLocPt h P.r) (hh' : D.IsLocPt h' P.r) (e : Wd.Ix (Fin w.length)) (ρ : M.Ty P) :
    Top.dH P l0 TT w (h ++ [(1, ζ)]) e ρ = Top.dH P l0 TT w (h' ++ [(1, ζ)]) e ρ := by
  simp only [Top.dH, wPt_app TT ζ h P.r hh, wPt_app TT ζ h' P.r hh']

theorem isLocPt_app (h : C.LPt) (n : ℕ) (hh : D.IsLocPt h n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    D.IsLocPt (h ++ [(1, ζ)]) (n + 1) := by
  refine ⟨fun b hb => ?_, ?_⟩
  · rcases List.mem_append.mp hb with hb | hb
    · exact hh.1 b hb
    · rw [List.mem_singleton] at hb
      subst hb
      exact ⟨le_rfl, hζ⟩
  · have := hh.2
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at this ⊢
    omega

def HeadCorr : Prop :=
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
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∃ (τ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (E' : M.Ty P → (Wp →L[ℂ] Wp)),
      (∀ U V, B.hsInner (τ U) (τ V) = B.hsInner U V) ∧
      (∀ ρ U, (p.TP.E ρ).comp (τ U) = τ ((E' ρ).comp U)) ∧
      (∀ ρ, (E' ρ).comp (E' ρ) = E' ρ) ∧ (∀ ρ (v v' : Wp), inner ℂ (E' ρ v) v' = inner ℂ v (E' ρ v')) ∧
      (∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        ∑ ρ : M.Ty P, (E' ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) =
          (y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) ∧
      (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (E' ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2)) ∧
      ∀ (h : C.LPt) (hh : D.IsLocPt h P.r)
        (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e, Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e) (KB.slv p.T F P.r le_rfl w h hh.2 e)) →
        ∀ e, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F)
            (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) =
          τ ((P5.act (Fr.ofWord L st (D.positionted w)).F Φ e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2)

def HeadTopOfCorr : Prop := HeadCorr → KB.HeadTop

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem head_top_of_correspondence : PBI.HeadTopOfCorr := by
  intro hC Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hdd hF hcut hΦ hΦ' x hx
  obtain ⟨τ, E', hτ, hint, hidem, hsa, hex, hd, hV⟩ := hC Wp Wq P p F w X μ L st Cb hD hdd hF hcut x hx
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hζ : ζ ≠ 0 := by
    have hG : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
      hx.2.2
    intro h0
    have hT := (p.T.bs P.r).T_pos
    have hT' := (p.T.bs P.r).T'_pos
    rw [h0, map_zero] at hG
    nlinarith [mul_pos hT hT']
  have hp := PBI.isLocPt_app h P.r hh ζ hζ
  have hq := PBI.isLocPt_app h' P.r hh' ζ hζ
  set y := P5.act (Fr.ofWord L st (D.positionted w)).F Φ with hy
  set y' := P5.act (Fr.ofWord L st (D.positionted w)).F Φ' with hy'
  have hVp : ∀ e, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(1, ζ)]) =
      τ ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) := hV h hh Φ hΦ
  have hVq : ∀ e, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h' ++ [(1, ζ)]) =
      τ ((y' e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) := hV h' hh' Φ' hΦ'
  have hLHS : P5.topDens L st (D.positionted w) Φ Φ' x.1 x.2 = ∑ e, ∑ ρ : M.Ty P,
      ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w (h ++ [(1, ζ)]) e ρ ^ 2 : ℝ) : ℂ) *
        B.hsInner ((E' ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2))
          ((y' e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) := by
    unfold P5.topDens
    refine Finset.sum_congr rfl fun e _ => ?_
    have hm := Formalism.FourierDecayAlt.P.Topx1.act_mul ((Fr.ofWord L st (D.positionted w)).d L) (Fr.ofWord L st (D.positionted w)).F Φ
    rw [hm, ← hy, hd h hh y e, Formalism.FourierDecayAlt.P.Topx1.hsInner_sum_smul_left]
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos ⟨hp, hq⟩, dif_neg (by omega), if_pos rfl, hLHS]
  by_cases hw : w = []
  · subst hw
    rw [if_pos rfl]
    haveI : Subsingleton (Wd.Ix (Fin ([] : List C.Letter).length)) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
    set e0 : Wd.Ix (Fin ([] : List C.Letter).length) := fun i => Fin.elim0 i
    rw [Finset.sum_eq_single e0 (fun b _ hb => absurd (Subsingleton.elim b e0) hb) (fun h => absurd (Finset.mem_univ e0) h)]
    have h1 := hVp e0
    have h2 := hVq e0
    rw [p.Θ.nil] at h1 h2
    rw [h1, h2, hτ]
    simp only [Formalism.FourierDecayAlt.P.Topx1.dH_nil, one_pow, Complex.ofReal_one, one_mul]
    have hs1 := Formalism.FourierDecayAlt.P.Topx1.hsInner_sum_smul_left (Finset.univ : Finset (M.Ty P)) (fun _ => (1 : ℂ))
      (fun ρ => (E' ρ).comp ((y e0 : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2))
      ((y' e0 : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2)
    simp only [one_smul, one_mul] at hs1
    rw [← hs1, hex y e0]
  · rw [if_neg hw]
    unfold Top.topOf
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
    rw [hVp e, hVq e, hint, hint, hτ,
      Formalism.FourierDecayAlt.P.Topx1.hsInner_proj (E' ρ) (hidem ρ) (hsa ρ),
      PBI.dH_app P p.l0 _ w ζ h' h hh' hh e ρ]
    push_cast
    ring

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.PBI

open Finset MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

def LevFrame {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) : Prop :=
  D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν' ∧
    D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀ ∧ D.IsBaseFrame (p.T.bs P.r) ν'r m₀r

def LevFrameExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    ∃ ν'r m₀r, LevFrame p ν'r m₀r

def HeadVec : Prop :=
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
      ∀ (h : C.LPt) (hh : D.IsLocPt h P.r)
        (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e, Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e) (KB.slv p.T F P.r le_rfl w h hh.2 e)) →
        ∀ e, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F)
            (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp))
            x.1 γ₀

def HeadTypes : Prop :=
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
    ∃ (τ : (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (E' : M.Ty P → (Wp →L[ℂ] Wp)),
      (∀ U V, B.hsInner (τ U) (τ V) = B.hsInner U V) ∧
      (∀ ρ U, (p.TP.E ρ).comp (τ U) = τ ((E' ρ).comp U)) ∧
      (∀ ρ, (E' ρ).comp (E' ρ) = E' ρ) ∧ (∀ ρ (v v' : Wp), inner ℂ (E' ρ v) v' = inner ℂ v (E' ρ v')) ∧
      (∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        ∑ ρ : M.Ty P, (E' ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) =
          (y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) ∧
      (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (E' ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2)) ∧
      ∀ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        τ ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2) =
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀

def HeadCorrOfParts : Prop := LevFrameExists → HeadVec → HeadTypes → HeadCorr

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem head_correspondence_of_parts : PBI.HeadCorrOfParts := by
  intro hLF hVec hTy Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut x hx
  obtain ⟨ν'r, m₀r, hLev⟩ := hLF Wp Wq P p
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hG : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ : ζ ≠ 0 := by
    intro h0
    have hT := (p.T.bs P.r).T_pos
    have hT' := (p.T.bs P.r).T'_pos
    rw [h0, map_zero] at hG
    nlinarith [mul_pos hT hT']
  have hpt : D.IsLocPt [(1, ζ)] (P.r - P.r + 1) := ⟨by simp [hζ], by simp [D.ptSize]⟩
  have hptG : 0 < D.ptG (Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z') (P.r - P.r)
      [(1, ζ)] := by
    have e1 : (D.ptMatN [(1, ζ)] (P.r - P.r + 1)).det = ζ := by
      rw [show P.r - P.r + 1 = 1 by omega]
      simp [D.ptMatN, D.ptEntry, Matrix.det_unique]
    have e0 : (D.ptMatN [(1, ζ)] (P.r - P.r)).det = 1 := by
      rw [show P.r - P.r = 0 by omega]
      simp
    unfold D.ptG
    rw [e1, e0]
    simpa using hG
  obtain ⟨γ₀, hγG, hγZ, hγF⟩ := Formalism.FourierDecayAlt.P.exists_isotropic_frame P.k (P.r - P.r) Wp Wq (p.T.bs P.r) ν'r m₀r
    [(1, ζ)] hLev.2.2 hpt hptG
  have hγζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ = ζ := by
    have hz1 : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ (Fin.last _) (Fin.last _) := by
      simp only [Q.zetaL, Zhat]
    rw [hz1, hγZ]
    simp [D.ptMatN, D.ptEntry]
  obtain ⟨τ, E', hτ, hint, hidem, hsa, hex, hd, htr⟩ :=
    hTy Wp Wq P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hγζ hγF
  refine ⟨τ, E', hτ, hint, hidem, hsa, hex, hd, fun h hh Φ hΦ e => ?_⟩
  rw [hVec Wp Wq P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hγζ hγF h hh Φ hΦ e, htr]

end Formalism.FourierDecayAlt.P
