import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr

open Matrix Finset MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section betaJ

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congrJ_left (D : RealPlaceData k r Wp Wq) {F F₂ G : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D F g = JF D F₂ g) : beta D F G = beta D F₂ G := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F₂ (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

theorem beta_congrJ_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ JF.Om k r D.z D.z', JF D G g = JF D G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ JF.Om k r D.z D.z' := hq hQ
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [h _ hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end betaJ

section formJ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1)) (w : List C.Letter)

theorem formLev_congrJ_left (x y x' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hx : ∀ a, JC.NiceCoef (T.bs j) ε (x a)) (hy : ∀ a, JC.NiceCoef (T.bs j) ε (y a))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x x' = D.formLev T s j w y x' := by
  have hQQ : ∀ Y p q, BcGood (T.bs j) ε (D.QQlev T s j Y p q) := fun Y p q => bcGood_tL s Y p q
  have hR := mn_rrop_closure bcGood_closed (D.QQlev T s j) hQQ (D.positionted w)
  unfold D.formLev
  refine Finset.sum_congr rfl fun a _ => beta_congrJ_left (T.bs j) fun h hh => ?_
  rw [bc_core (D.RRlev T s j w) hR x hx a hh, bc_core (D.RRlev T s j w) hR y hy a hh]
  show (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (x b) g)) h =
    (∑ b, D.ap (D.RRlev T s j w a b) (fun g => B.JF (T.bs j) (y b) g)) h
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact (hR a b).2.2 _ _ (fun g hg hgG => hJ b g ⟨hgG, hg⟩) h hh.2 hh.1

theorem formLev_congrJ_right (x' x y : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (hJ : ∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) :
    D.formLev T s j w x' x = D.formLev T s j w x' y := by
  unfold D.formLev
  exact Finset.sum_congr rfl fun a _ => beta_congrJ_right (T.bs j) (hJ a)

theorem pairJ_congrJ_left (ε : ℝ) : ∀ (ys : List ℝ)
    (x y : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x' : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, JC.NiceCoef (T.bs j) ε (x a)) → (∀ a, JC.NiceCoef (T.bs j) ε (y a)) →
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x x' = KB.pairJ (D.formLev T s j w) ys y x'
  | [], x, y, x', hx, hy, hJ => formLev_congrJ_left P0 T s j w x y x' ε hx hy hJ
  | _ :: ys, x, y, x', hx, hy, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_left ε ys (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _),
      pairJ_congrJ_left ε ys (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) _ (fun _ => hx _)
      (fun _ => hy _) (fun _ => hJ _)]

theorem pairJ_congrJ_right : ∀ (ys : List ℝ)
    (x' : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
    (x y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)),
    (∀ a, ∀ g ∈ JF.Om P0.k (P0.r - j) (T.bs j).z (T.bs j).z', B.JF (T.bs j) (x a) g = B.JF (T.bs j) (y a) g) →
    KB.pairJ (D.formLev T s j w) ys x' x = KB.pairJ (D.formLev T s j w) ys x' y
  | [], x', x, y, hJ => formLev_congrJ_right P0 T s j w x' x y hJ
  | _ :: ys, x', x, y, hJ => by
    simp only [KB.pairJ]
    rw [pairJ_congrJ_right ys _ (fun e => x (Fin.cons 0 e)) (fun e => y (Fin.cons 0 e)) (fun _ => hJ _),
      pairJ_congrJ_right ys _ (fun e => x (Fin.cons 1 e)) (fun e => y (Fin.cons 1 e)) (fun _ => hJ _)]

end formJ

end Formalism.FourierDecayAlt.P.PBG
