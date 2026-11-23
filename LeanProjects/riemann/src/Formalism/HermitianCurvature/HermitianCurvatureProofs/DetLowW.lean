import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVZeroOfVanish
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBSupp

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_agree {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (l : Fin (r + 2)) (a : ℂ) (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV k r, Dmin k r Bs.z Bs.z' g l = a → H₁ g = H₂ g) (y : B.Mat k r) (hy : y ∈ B.GV k r)
    (hya : Dmin k r Bs.z Bs.z' y l = a) : PBG.Kr Bs H₁ y = PBG.Kr Bs H₂ y := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  have hg : y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hξ.2.1) hξ.1.1
  rw [hH _ hg (by rw [PBG.dmin_pR Bs hξ y l, hya])]

theorem pbT_agree (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (a : ℂ)
    (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a → H₁ g = H₂ g)
    (g : B.Mat P.k P.r) (hg : g ∈ B.GV P.k P.r)
    (hga : Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a) :
    pbT p j (by omega) H₁ g = pbT p j (by omega) H₂ g := by
  unfold pbT
  have e : j + (P.r - j) = P.r := by omega
  rw [PartialBesselProperness.pbF_eq_TI, PartialBesselProperness.pbF_eq_TI]
  unfold PartialBesselProperness.TI
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [PartialBesselProperness.gI]
  split_ifs with hx
  · have hs : PartialBesselProperness.sE (p.T.bs j) e x ∈ Sset P.k P.r p.T.base.z := by
      have := PartialBesselProperness.sE_mem_S (p.T.bs j) e x
      rwa [p.T.z_lev j (by omega)] at this
    have hyG : PartialBesselProperness.sE (p.T.bs j) e x * g ∈ B.GV P.k P.r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (PartialBesselProperness.sE_GV _ e x) hg
    have hyD : Dmin P.k P.r p.T.base.z p.T.base.z' (PartialBesselProperness.sE (p.T.bs j) e x * g) ⟨j + 1, by omega⟩ = a := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds P.k P.r p.T.base.z p.T.base.z' p.T.base.z_mem p.T.base.z'_mem _ hs 1
        (Formalism.FourierDecayAlt.P.PBG.one_mem_Sset P.k P.r _) g ⟨j + 1, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this, hga]
    rw [kr_agree p.T.base ⟨j + 1, by omega⟩ a H₁ H₂ hH _ hyG hyD]
  · rfl

def aVal (h : C.LPt) (t : ℂ) : ℂ := (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)) (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    KB.CptCoef p.T.base Fc →
    (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
      Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
    B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
      B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 fun a => a.elim0) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (t : ℂ), D.IsLocPt (h ++ [(1, t)]) (j + 1) → ∀ e : Wd.Ix (Fin w.length),
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
      ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : (U.lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [U.lowW]
  · intro a b hab
    simp only [U.lowW, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    have hab' : a < b := hab
    rw [if_neg (ne_of_lt hab'), dif_neg (fun h => absurd h.1 (not_lt.mpr hab'.le)), add_zero]

theorem zxH_det (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (v : XH h) :
    (zxH h j hh.2 v).det = (U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (CutHB.ptDiag_ne hh)
  have hw : IsUnit (U.wP (D.ptPerm h)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    apply hH
    rw [U.hMat, Matrix.det_mul, h0, zero_mul]
  unfold zxH LeftFubiniLemmas.lhOf
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conj hw, det_lowW, one_mul]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
