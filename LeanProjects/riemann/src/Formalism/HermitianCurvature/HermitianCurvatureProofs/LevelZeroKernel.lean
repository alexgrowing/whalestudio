import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective

open Matrix MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section defs

variable {k r : ℕ}

def zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : Matrix (Fin (j + 1)) (Fin (j + 1)) ℂ :=
  U.blk2 Z 0 0 (Matrix.of fun _ _ => τ)

def x0 (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))) : B.Mat k r :=
  D.castM (by omega : j + 1 + (r - (j + 1)) = r) (U.mMap k (j + 1) (r - (j + 1)) (zfull Z τ) γ)

def nL (k r j : ℕ) (hj : j + 1 ≤ r) (a : Fin j → ℂ) : B.Mat k r :=
  1 + ∑ b : Fin j, (a b • Matrix.single (esI k r ⟨j, by omega⟩) (esI k r ⟨b, by omega⟩) (1 : ℂ) -
    conj (a b) • Matrix.single (eI k r ⟨b, by omega⟩) (eI k r ⟨j, by omega⟩) (1 : ℂ))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def RulesOn (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E) :
    Prop :=
  Q.SmoothLev k r 0 Dm Φ ∧
    (∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ n ∈ QuantumDeterminants.Nset k r, g * n ∈ Dm ∧ Φ (g * n) = psi k r z' cStd n • Φ g) ∧
    ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, nL k r j hj a * g ∈ Dm ∧
      Φ (nL k r j hj a * g) = psi k r z cStd (nL k r j hj a) • Φ g

def levelZeroKernel (k r j : ℕ) : ℂ := ((r - j : ℕ) : ℂ) + (k : ℂ) / 2

def domJ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) :=
  {g | Dmin k r z z' g ⟨j, by omega⟩ ≠ 0 ∧ Dmin k r z z' g ⟨j + 1, by omega⟩ ≠ 0 ∧ 0 < Gf k r z z' g}

def ParamComm {j : ℕ} (A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E)) : Prop :=
  ∀ (U : Set (ℂ × (Fin j → Fin j → ℂ))) (κ : ℂ → Matrix (Fin j) (Fin j) ℂ → E), IsOpen U →
    U ⊆ {q | (Matrix.of q.2).det ≠ 0} →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => κ q.1 (Matrix.of q.2)) U →
    ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => A (κ q.1) (Matrix.of q.2)) U ∧
    ∀ q ∈ U, PBP.dz (fun τ => A (κ τ) (Matrix.of q.2)) q.1 = A (fun Z => PBP.dz (fun τ => κ τ Z) q.1) (Matrix.of q.2) ∧
      PBP.dzb (fun τ => A (κ τ) (Matrix.of q.2)) q.1 = A (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) (Matrix.of q.2)

end defs

def HeadLetter : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))) (τ : ℂ), Z.det ≠ 0 → τ ≠ 0 →
    γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm → ∀ Y : ℝ,
      D.vLet k r z z' (j + 1) hj (true, Y) 0 Φ (x0 k r j hj Z τ γ) =
          ((Y : ℂ) + levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) +
            τ • PBP.dz (fun τ' => D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
            τ • D.vLet k r z z' j (by omega) (true, Y) 1 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (true, Y) 1 Φ (x0 k r j hj Z τ γ) =
          τ⁻¹ • D.vLet k r z z' j (by omega) (true, Y) 0 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (false, Y) 0 Φ (x0 k r j hj Z τ γ) =
          ((Y : ℂ) - levelZeroKernel k r j) • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ) -
            conj τ • PBP.dzb (fun τ' => D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ' γ)) τ -
            conj τ • D.vLet k r z z' j (by omega) (false, Y) 1 Φ (x0 k r j hj Z τ γ) ∧
      D.vLet k r z z' (j + 1) hj (false, Y) 1 Φ (x0 k r j hj Z τ γ) =
          (conj τ)⁻¹ • D.vLet k r z z' j (by omega) (false, Y) 0 Φ (x0 k r j hj Z τ γ)

def ZOnly : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (l : C.Letter) (e : Fin 2), inWb k r z → inWb k r z' →
    ∃ A : (Matrix (Fin j) (Fin j) ℂ → E) →ₗ[ℂ] (Matrix (Fin j) (Fin j) ℂ → E), ParamComm A ∧
      ∀ (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), IsOpen Dm → Dm ⊆ domJ k r j hj z z' → Q.SmoothLev k r 0 Dm Φ →
      ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → τ ≠ 0 →
        γ ∈ B.GV k (r - (j + 1)) → x0 k r j hj Z τ γ ∈ Dm →
        D.vLet k r z z' j (by omega) l e Φ (x0 k r j hj Z τ γ) = A (fun Z' => Φ (x0 k r j hj Z' τ γ)) Z

def RulesClosed : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (i : ℕ) (hi : i ≤ j + 1), (i = j ∨ i = j + 1) → ∀ (l : C.Letter) (e : Fin 2),
      RulesOn k r j hj z z' Dm (D.vLet k r z z' i (by omega) l e Φ)

def WordInd : Prop :=
  ∀ (k r j : ℕ) (hj : j + 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Dm : Set (Q.Mx k r)) (Φ : Q.Mx k r → E), inWb k r z → inWb k r z' → IsOpen Dm →
    Dm ⊆ domJ k r j hj z z' → RulesOn k r j hj z z' Dm Φ →
    ∀ (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k (r - (j + 1))), Z.det ≠ 0 → γ ∈ B.GV k (r - (j + 1)) →
    (∀ τ : ℂ, τ ≠ 0 → x0 k r j hj Z τ γ ∈ Dm) →
    ∀ (w : List C.Letter) (φ : Wd.Ix (Fin w.length) → V1 E),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = D.uwG k r z z' Φ j (by omega) w e (x0 k r j hj Z τ γ)) →
    ∀ (t : ℂ), t ≠ 0 → ∀ e, D.uwG k r z z' Φ (j + 1) hj w e (x0 k r j hj Z t γ) =
      (oneBT (levelZeroKernel k r j) (D.positionted w) φ e).1 t

def WordIndOfParts : Prop := HeadLetter → ZOnly → RulesClosed → WordInd

def HeadBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp),
    (∀ e τ, τ ≠ 0 → (φ e).1 τ = B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 e) (mLev P j hj τ γ)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
    ∃ (X : Type) (_ : MeasurableSpace X) (μ : Measure X) (ℓ : X → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
      (Zx : X → Matrix (Fin j) (Fin j) ℂ) (Fx : X → Q.Mx P.k P.r → (Wq →L[ℂ] Wp)) (Dm : Set (Q.Mx P.k P.r))
      (φx : X → Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp)),
      IsOpen Dm ∧ Dm ⊆ domJ P.k P.r j hj p.T.base.z p.T.base.z' ∧
      (∀ x, RulesOn P.k P.r j hj p.T.base.z p.T.base.z' Dm (Fx x)) ∧
      (∀ x, (Zx x).det ≠ 0 ∧ ∀ τ : ℂ, τ ≠ 0 → x0 P.k P.r j hj (Zx x) τ γ ∈ Dm) ∧
      (∀ x e' τ, τ ≠ 0 → (φx x e').1 τ =
        D.uwG P.k P.r p.T.base.z p.T.base.z' (Fx x) j (by omega) w e' (x0 P.k P.r j hj (Zx x) τ γ)) ∧
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        ∫ x, ℓ x (D.uwG P.k P.r p.T.base.z p.T.base.z' (Fx x) (j + 1) hj w e (x0 P.k P.r j hj (Zx x) t γ)) ∂μ ∧
      (oneBT (kapJ P j) (D.positionted w) φ e).1 t = ∫ x, ℓ x ((oneBT (kapJ P j) (D.positionted w) (φx x) e).1 t) ∂μ

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
