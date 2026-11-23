import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section defs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

def cc (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) : Fin (P.r - j) → ℂ :=
  fun l => consC t c (Fin.cast (by omega) l)

def gi (j : ℕ) (hj : j + 1 ≤ P.r) (g : Mx P.k (P.r - (j + 1))) : Mx P.k (P.r - j) :=
  D.castM (by omega) (ιLev P.k 1 (P.r - (j + 1)) g)

def GoodFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ t₀ : ℂ, t₀ ≠ 0 → ∀ γ₀ ∈ B.GV P.k (P.r - (j + 1)), ∃ (U : Set (ℂ × B.Mat P.k (P.r - (j + 1))))
      (f : ℂ × B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), IsOpen U ∧ (t₀, γ₀) ∈ U ∧ ContDiffOn ℝ ∞ f U ∧
      ∀ p ∈ U, p.2 ∈ B.GV P.k (P.r - (j + 1)) → G p.1 p.2 = f p) ∧
  ∀ K : Set ℂ, IsCompact K → (∀ t ∈ K, t ≠ 0) → ∃ C : Set (B.Mat P.k (P.r - (j + 1))), IsCompact C ∧
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ K, ∀ γ, G t γ ≠ 0 → γ ∈ C ∧
      (γ ∈ B.GV P.k (P.r - (j + 1)) → ε ≤ Gf P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' γ)

def famP (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) (v : ℂ) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ => fderiv ℝ (fun u : ℂ => G u γ) t v

def Rep (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
    (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def InC (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') : Prop :=
  ∃ G, GoodFam T j G ∧ Rep T j hj Ψ G

def sliceFam (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) :
    ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp) :=
  fun t => (B.GV P.k (P.r - (j + 1))).indicator fun γ =>
    ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
        F ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ * mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ *
          rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
      ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

end defs

def FamJFOK : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ t : ℂ, t ≠ 0 → JFOKCpt (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (G t)

def FamAlg : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → GoodFam T j G' → ∀ m : ℂ → ℂ, ContDiffOn ℝ ∞ m {t | t ≠ 0} →
      GoodFam T j (fun t γ => G t γ + G' t γ) ∧ GoodFam T j (fun t γ => m t • G t γ)

def FamDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)),
    GoodFam T j G → ∀ v : ℂ, GoodFam T j (famP j G v)

def RepLin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G G' : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G → GoodFam T j G' →
    ∀ t : ℂ, t ≠ 0 → ∀ (a : ℂ), ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => G t γ + G' t γ)) x.1 x.2 =
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2 +
            resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G' t)) x.1 x.2 ∧
        resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (fun γ => a • G t γ)) x.1 x.2 =
          a • resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G t)) x.1 x.2

def FamJFDeriv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ), j + 1 ≤ P.r →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp)), GoodFam T j G →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z', ∀ v : ℂ,
      HasDerivAt (fun s : ℝ =>
          resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (G (t + (s : ℂ) * v))) x.1 x.2)
        (resG P.k (P.r - (j + 1)) (Fin.last _) (B.JF (T.bs (j + 1)) (famP j G v t)) x.1 x.2) 0

def CellTie : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ t : ℂ, t ≠ 0 → ∀ x ∈ DomR P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z',
      (cc j hj t x.1, gi j hj x.2) ∈ DomR P.k (P.r - j) (T.bs j).z (T.bs j).z' ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ B.GV P.k (P.r - (j + 1)) ∧
        wCell P.k (P.r - (j + 1)) (Fin.last _) x.1 * x.2 ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z'

def SliceFamGood : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
      GoodFam T j (sliceFam T j hj F)

def SliceFamJF : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp), JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F →
    ∀ t : ℂ, t ≠ 0 → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
      γ ∈ OmPlus P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' →
      B.JF (T.bs (j + 1)) (sliceFam T j hj F t) γ =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • B.JF (T.bs j) F (mc (by omega : P.r - (j + 1) + 1 = P.r - j) t γ)

def OpClosed : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq), IsPlace P T.base.z T.base.z' T.base.π T.base.π' → D.TowerNormalised T →
    ∀ (j : ℕ) (hj : j + 1 ≤ P.r),
    IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →
    IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' →
    ∀ (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (i : Fin 6)
      (Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      InC T j hj Ψ → InC T j hj (X.op ⟨0, by omega⟩ i Ψ)

def BTlAdjoin : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r), IsActualLevel X L →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (l : Fin r) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S),
      (bTl L l w a b).1 ∈ Algebra.adjoin ℂ (Set.range (X.op l))

def UUiwScalar : Prop :=
  ∀ (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (S : Type) [Fintype S] [DecidableEq S] (s : ℂ)
    (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S), Wd.UUiw (A := A) s w a b ∈ (⊥ : Subalgebra ℂ A)

end Formalism.FourierDecayAlt.P.CutSH
