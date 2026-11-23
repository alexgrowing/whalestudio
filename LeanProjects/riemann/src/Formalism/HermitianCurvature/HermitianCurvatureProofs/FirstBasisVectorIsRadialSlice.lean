import Formalism.HermitianCurvature.HermitianCurvatureProofs.CastMIotaSelf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadPictureEmptyWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def StepHyp (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')))
    (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T G j (by omega) w h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted w)) Ψ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T G (j + 1) hj w (h ++ [(1, t)]) ht.2 e)) y.1 y.2

def sW (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (e : Wd.Ix (Fin w.length)) (q : C.LPt) (hq : D.ptSize q = P.r) : B.Mat P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
  D.castF (by rw [hq]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) q)

theorem castF_slice_congr {k r a : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) {q q' : C.LPt} (hq : q = q')
    (p1 : a = r - D.ptSize q) (p2 : a = r - D.ptSize q') :
    D.castF p1 (D.sliceAt k r z z' F q) = D.castF p2 (D.sliceAt k r z z' F q') := by
  subst hq; rfl

theorem listProd_zero {A : Type*} [Monoid A] {n : ℕ} (hn : n = 0) (f : Fin n → A) :
    ((List.finRange n).reverse.map f).prod = 1 := by
  subst hn; rfl

theorem smul_inv_real {V : Type*} [AddCommGroup V] [Module ℂ V] {a : ℝ} (ha : a ≠ 0) (v : V) :
    ((a : ℝ) : ℂ) • (((a⁻¹ : ℝ) : ℂ) • v) = v := by
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha, Complex.ofReal_one, one_smul]

theorem core (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (hst : StepHyp P p G w) :
    ∀ (m j : ℕ), P.r - j = m → ∀ (hjr : j ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')))
    (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T G j hjr w h hh.2 e)) →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin (P.r - j) → ℂ), c ∈ OmX (P.r - j) →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L (D.positionted w)) Ψ e : Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c
          (D.castM (by change (P.r - j) + (P.r - P.r) = P.r - j; omega) (ιLev P.k (P.r - j) (P.r - P.r) g)) =
        ((∏ i : Fin (P.r - j), ‖c i‖ ^ (2 * ((P.r - j) - (i : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (sW P p G w e (h ++ PBI.hcell c)
            (by rw [ptSize_append, hh.2, PBI.ptSize_hcell]; omega)) g := by
  have h0 : P.r - P.r = 0 := Nat.sub_self _
  intro m
  induction m with
  | zero =>
    intro j hjm hjr h hh X μ L st Ψ hD hΨ e c hc g hg hgG
    obtain rfl : j = P.r := by omega
    have hb : P5.bTall L (D.positionted w) = 1 := listProd_zero h0 _
    rw [hb, show P5.act (1 : Wd.SlopeTestRemainingChoices _ _) Ψ = Ψ from Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Ψ]
    have hcg : D.castM (by omega : (P.r - P.r) + (P.r - P.r) = P.r - P.r) (ιLev P.k (P.r - P.r) (P.r - P.r) g) = g :=
      castM_iota_self h0 _ g
    refine (congrArg (fun g' => ((Ψ e).1 : Q.Fn P.k (P.r - P.r) (Wq →L[ℂ] Wp)) c g') hcg).trans ?_
    refine (hΨ e (c, g) ⟨hc, hg, hgG⟩).trans ?_
    refine (resG_empty h0 _ _ _).trans ?_
    have hp1 : (∏ i : Fin (P.r - P.r), ‖c i‖ ^ (2 * ((P.r - P.r) - (i : ℕ)) + P.k)) = 1 := by
      have : IsEmpty (Fin (P.r - P.r)) := ⟨fun i => by have := i.2; omega⟩
      simp
    have hfin : B.JF (p.T.bs P.r) (KB.slv p.T G P.r hjr w h hh.2 e) g =
        ((∏ i : Fin (P.r - P.r), ‖c i‖ ^ (2 * ((P.r - P.r) - (i : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (sW P p G w e (h ++ PBI.hcell c)
            (by rw [ptSize_append, hh.2, PBI.ptSize_hcell]; omega)) g := by
      rw [hp1, Complex.ofReal_one, one_smul]
      exact congrArg (fun F => B.JF (p.T.bs P.r) F g)
        (castF_slice_congr _ _ _ (by rw [hcell_nil h0 c, List.append_nil]) _ _)
    exact hfin
  | succ m ih =>
    intro j hjm hjr h hh X μ L st Ψ hD hΨ e c hc g hg hgG
    have hj : j + 1 ≤ P.r := by omega
    have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

    have hPl : IsPlace (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
        (p.T.bs (j + 1)).π' := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨j + 1, by omega⟩ p.hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
        (p.T.bs (j + 1)).π' Xs μs Ls sts p.l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩

    obtain ⟨t, c', rfl⟩ := exists_cons hn c
    obtain ⟨ht0, hc'⟩ := omX_cons hn hc
    have ht : D.IsLocPt (h ++ [(1, t)]) (j + 1) := Formalism.FourierDecayAlt.P.PBP.isLocPt_snoc hh ht0
    obtain ⟨T, hTr, hTall⟩ := bTall_cast (k := (JC.parLev P j).k) (n := (JC.parLev P j).r)
      (ρ := (JC.parLev P (j + 1)).r) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (PBH.tower_π p.T j hj) (PBH.tower_π' p.T j hj) X Xs L Ls hD.2.2.1 hDs.2.2.1 ht0
    have e2 : P.r - (j + 1) + (P.r - P.r) = P.r - (j + 1) := by omega
    set g2 := D.castM e2 (ιLev P.k (P.r - (j + 1)) (P.r - P.r) g) with hg2
    have hι := iota_split (k := P.k) hn h0 (by omega) e2 g
    refine (congrArg (fun g' => ((P5.act (P5.bTall L (D.positionted w)) Ψ e).1 : Q.Fn P.k (P.r - j) (Wq →L[ℂ] Wp))
      (fun l => PBH.consC t c' (Fin.cast hn.symm l)) g') hι).trans ?_
    have key := hTr (P5.act (P5.bTall L (D.positionted w)) Ψ e) c' g2
    refine key.symm.trans ?_
    refine (congrArg (fun Φ => (Φ.1 : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c' g2)
      (hTall _ (D.positionted w) Ψ e)).trans ?_

    set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
    have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht0)
    let Ψ' : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (p.T.bs (j + 1)).z
        (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π (p.T.bs (j + 1)).π' :=
      fun a => ((lam⁻¹ : ℝ) : ℂ) • T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)
    have hΨ' : ∀ a, Top.IsRadOf (JC.parLev P (j + 1)) (p.T.bs (j + 1)) (Ψ' a)
        (KB.slv p.T G (j + 1) hj w (h ++ [(1, t)]) ht.2 a) := by
      intro a y hy
      have e1 := hTr (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a) y.1 y.2
      have e3 := hst j hj h hh X μ L st Ψ hD hΨ t ht a y hy
      have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
        rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
      exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e3)).trans (hcl _)
    have hfun : (fun a => ((lam : ℝ) : ℂ) • Ψ' a) =
        (fun a => T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)) := by
      funext a
      exact smul_inv_real hlam0 _
    have hA : P5.act (P5.bTall Ls (D.positionted w)) (fun a => T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)) e =
        ((lam : ℝ) : ℂ) • P5.act (P5.bTall Ls (D.positionted w)) Ψ' e :=
      (congrArg (fun x => P5.act (P5.bTall Ls (D.positionted w)) x e) hfun).symm.trans
        (congrFun (Formalism.FourierDecayAlt.P.PBP.act_smul' (P5.bTall Ls (D.positionted w)) Ψ' ((lam : ℝ) : ℂ)) e)
    refine (congrArg (fun Φ => (Φ.1 : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c' g2) hA).trans ?_
    have IH := ih (j + 1) (by omega) hj (h ++ [(1, t)]) ht Xs μs Ls sts Ψ' hDs hΨ' e c' hc' g hg hgG
    refine (congrArg (fun v => ((lam : ℝ) : ℂ) • v) IH).trans ?_
    have hP : ((lam : ℝ) : ℂ) * ((∏ i : Fin (P.r - (j + 1)), ‖c' i‖ ^ (2 * ((P.r - (j + 1)) - (i : ℕ)) + P.k) : ℝ) : ℂ) =
        ((∏ i : Fin (P.r - j), ‖PBH.consC t c' (Fin.cast hn.symm i)‖ ^ (2 * ((P.r - j) - (i : ℕ)) + P.k) : ℝ) : ℂ) := by
      rw [prod_cons hn, Complex.ofReal_mul]
    have hq : (h ++ [(1, t)]) ++ PBI.hcell c' = h ++ PBI.hcell (fun l => PBH.consC t c' (Fin.cast hn.symm l)) := by
      rw [hcell_cons hn, List.append_assoc]
      rfl
    rw [smul_smul]
    exact congr_arg₂ (fun (a : ℂ) (F : B.Mat P.k (P.r - P.r) → (Wq →L[ℂ] Wp)) => a • B.JF (p.T.bs P.r) F g) hP
      (castF_slice_congr _ _ _ hq _ _)

theorem first_basis_vector_isRadial (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (ΦG : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (hΦG : Top.IsRadOf P p.T.base ΦG G)
    (e : Wd.Ix (Fin w.length)) :
    Top.IsRadOf P p.T.base (Top.firstStateVector ΦG e) (if e = Wd.e1 then G else 0) := by
  intro x hx
  by_cases he : e = Wd.e1
  · rw [show Top.firstStateVector ΦG e = ΦG from if_pos he, if_pos he]
    exact hΦG x hx
  · rw [show Top.firstStateVector ΦG e = 0 from if_neg he, if_neg he]
    have hz : B.JF p.T.base (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun _ => 0 :=
      funext fun g => Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero (Bs := p.T.base) g
    rw [hz]
    simp [Q.resG]

theorem first_basis_vector_isRadial_slice (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (ΦG : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (hΦG : Top.IsRadOf P p.T.base ΦG G)
    (e : Wd.Ix (Fin w.length)) :
    Top.IsRadOf (JC.parLev P 0) (p.T.bs 0) (Top.firstStateVector ΦG e) (KB.slv p.T G 0 (Nat.zero_le _) w [] rfl e) := by
  have hfun : KB.slv p.T G 0 (Nat.zero_le _) w [] rfl e = if e = Wd.e1 then G else 0 := by
    funext γ
    have hcm : D.castM (k := P.k) (a := P.r - 0) (b := P.r - D.ptSize []) rfl γ = γ := by
      ext i j; rfl
    simp only [KB.slv, D.castF]
    rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil P.k P.r _ _ p.T.base.z_mem p.T.base.z'_mem,
      Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
  have h0 := first_basis_vector_isRadial P p G w ΦG hΦG e
  intro x hx
  refine (h0 x hx).trans ?_
  exact congrArg (fun F : B.Mat P.k P.r → (Wq →L[ℂ] Wp) =>
    Q.resG P.k P.r (Fin.last P.r) (B.JF p.T.base F) x.1 x.2) hfun.symm

theorem isLocPt_nil : D.IsLocPt [] 0 := ⟨fun b hb => by simp at hb, rfl⟩

end core

end Formalism.FourierDecayAlt.P.FinRangeListSplitting

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.FinRangeListSplitting

theorem pb_radWordSliceOfHeadPic (hHP : PBP.HeadPic) : PBI.RadWordSlice := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ hD₀ G hG w hcut ΦG hΦG e c hc g hg hgG
  have hst : StepHyp P p G w := fun j hj h hh X μ L st Ψ hD hΨ t ht a y hy =>
    hHP Wp Wq P p G j hj w h hh X μ L st Ψ hD hG hcut hΨ t ht a y hy
  exact core P p G w hst (P.r - 0) 0 rfl (Nat.zero_le _) [] isLocPt_nil X₀ μ₀ L₀ st₀ (Top.firstStateVector ΦG) hD₀
    (first_basis_vector_isRadial_slice P p G w ΦG hΦG) e c hc g hg hgG

theorem level_zero_picture_of_slice : PBI.PicSlice := by
  intro Wp Wq _ _ _ _ _ _ P p G hG ΦG hΦG c hc g hg hgG
  have hst : StepHyp P p G [] := fun j hj h hh X μ L st Ψ hD hΨ t ht a y hy =>
    Formalism.FourierDecayAlt.P.head_picture_empty_word Wp Wq P p G j hj h hh L Ψ hG hΨ t ht a y hy
  have hPl : IsPlace (JC.parLev P 0) (p.T.bs 0).z (p.T.bs 0).z' (p.T.bs 0).π (p.T.bs 0).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨0, by omega⟩ p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (p.T.bs 0)
  have hD : P5.IsData (JC.parLev P 0) (p.T.bs 0).z (p.T.bs 0).z' (p.T.bs 0).π (p.T.bs 0).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  have key := core P p G [] hst (P.r - 0) 0 rfl (Nat.zero_le _) [] isLocPt_nil X μ L st (Top.firstStateVector ΦG) hD
    (first_basis_vector_isRadial_slice P p G [] ΦG hΦG) (fun _ => 0) c hc g hg hgG
  have hb0 : P5.bTall L (D.positionted ([] : List C.Letter)) = 1 := by
    unfold P5.bTall
    have h1 : ∀ l, P5.bTl L l (D.positionted ([] : List C.Letter)) = 1 := fun l => rfl
    simp [h1]
  have hL : P5.act (P5.bTall L (D.positionted ([] : List C.Letter))) (Top.firstStateVector ΦG) (fun _ => 0) = ΦG := by
    rw [hb0]
    exact (congrFun (Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ (Top.firstStateVector ΦG)) _).trans (if_pos rfl)
  exact (congrArg (fun Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' =>
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) hL).symm.trans key

end Formalism.FourierDecayAlt.P
