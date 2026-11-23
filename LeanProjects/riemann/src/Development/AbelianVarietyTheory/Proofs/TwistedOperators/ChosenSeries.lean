import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.BarMatrix
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ContractionTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LPol (b a : ℕ) : Type := MvPolynomial (Fin b × Fin a) ℂ

section Local

variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

def rai (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (i, j))
    else -(MvPolynomial.pderiv (i, j)).toLinearMap)

def low (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (i, j)))

def locS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def locT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def IsPolyIso {p q r s : ℕ} (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b) (κ : LPol b a ≃ₗ[ℂ] Pol p q r s) : Prop :=
  (∀ (Z : Mat p q) (P : LPol b a), κ (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (κ P)) ∧
    ∀ (Z : Mat r s) (P : LPol b a), κ (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (κ P)

end Local

structure IsCoverIt {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) : Prop where
  bdd : ∀ P, ∃ c : ℝ, ∀ y, ‖B P y‖ ≤ c * ‖y‖
  kfin : ∀ P y, B P y ∈ Set.range R₁.ι
  ne : ∀ y, y ≠ 0 → ∃ P, B P y ≠ 0
  src : ∀ Z ∈ upq p q, ∀ P y,
    HasDerivAt (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) (B (fockAct1 p q r s Z P) y) 0
  tgt : ∀ Z ∈ upq r s, ∀ P y,
    HasDerivAt (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) (-B (fockAct2 p q r s Z P) y) 0

variable {D : D7}

def glue {a b : ℕ} (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)

open Classical in

def GlueLaw (D : D7) (a b : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ ∧
    ∀ (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : D.what₂.Tau → LPol b a),
      (∀ X, fockS τ ε ε' X (glue P) = glue (Function.update P τ (locS ε ε' X (P τ)))) ∧
        ∀ Y, fockT τ ε ε' Y (glue P) = glue (Function.update P τ (locT ε ε' Y (P τ)))

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure LocIt (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ) : Prop where
  sm : ∀ P y, A P y ∈ M.sm τ
  ne : ∃ P, ∃ y ∈ M'.sm τ, A P y ≠ 0
  adj : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (A P y))
    (A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y) 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P y, HasDerivAt (fun t : ℝ => A P (M'.rep τ (NormedSpace.exp (t • Y)) y))
    (-A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y) 0

def srcOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tgtOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure GlobIt (aS aT : D.what₂.Tau → ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) : Prop where
  incl : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v)
  ne : It ≠ 0
  adj : ∀ φ w, ellT M w ∘ₗ I φ ∈ Submodule.span ℂ (Set.range (ellT M'))
  src : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (I φ x)))
      (ellT M w (I (srcOp M M' τ (aT τ) X φ) x)) 0
  tgt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (I φ (actT M' τ (NormedSpace.exp (t • Y)) x)))
      (-ellT M w (I (tgtOp M M' τ (aS τ) Y φ) x)) 0

structure TensorLaw : Prop where
  sep : ∀ x : ⨂[ℂ] τ, M.H τ, (∀ w, ellT M w x = 0) → x = 0
  inj : Function.Injective (inclT M)
  one : ∀ τ, actT M τ 1 = LinearMap.id
  mul : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actT M τ (g * g') = actT M τ g ∘ₗ actT M τ g'
  adj : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, ∃ w', ellT M w ∘ₗ actT M τ g = ellT M w'

def ChosenSeries (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam

end GlobalTheory.Chain.RealIt

end
