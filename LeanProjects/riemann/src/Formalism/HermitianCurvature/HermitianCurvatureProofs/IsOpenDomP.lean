import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

abbrev XH (h : C.LPt) : Type := U.LW (D.ptPerm h) → ℂ

def ellH (h : C.LPt) (v : XH h) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h) v)) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)

def zxH (h : C.LPt) (j : ℕ) (hh : D.ptSize h = j) (v : XH h) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.reindex (finCongr hh) (finCongr hh) (LeftFubiniLemmas.lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h))

def pbT (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    Q.Mx P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) F g

def domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) :=
  {g | (∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0) ∧ 0 < Gf k r z z' g}

theorem isOpen_domP (k r j : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (domP k r j z z') := by
  have h1 : IsOpen {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
    have : {g : Q.Mx k r | ∀ l : Fin (r + 2), j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} =
        ⋂ l : Fin (r + 2), {g | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} := by
      ext g; simp
    rw [this]
    refine isOpen_iInter_of_finite fun l => ?_
    by_cases hl : j ≤ l.val ∧ l.val ≤ r
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
        ext g; simp [hl.1, hl.2]
      rw [this]
      exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous continuous_const
    · have : {g : Q.Mx k r | j ≤ l.val → l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
        ext g; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro a b; exact absurd ⟨a, b⟩ hl
      rw [this]; exact isOpen_univ
  exact h1.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf z z').continuous)

theorem minorDomain_subset (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    domP k r j z z' ⊆ LevelPointCoordinates.domJ k r j hj z z' := fun g hg =>
  ⟨hg.1 ⟨j, by omega⟩ (show j ≤ j from le_rfl) (show j ≤ r by omega),
    hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ r by omega), hg.2⟩

end Formalism.FourierDecayAlt.P.PBQ
