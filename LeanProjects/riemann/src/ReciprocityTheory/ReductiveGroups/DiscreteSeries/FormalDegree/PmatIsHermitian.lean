import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def dk (ε : Fin n → Bool) : Measure (KG ε) := (muK ε Set.univ)⁻¹ • muK ε

abbrev PCoord (ε : Fin n → Bool) : Type := {ab : Fin n × Fin n // ab.2 < ab.1 ∧ ε ab.1 ≠ ε ab.2}

def pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Matrix (Fin n) (Fin n) ℂ := fun a b =>
  if h : b < a ∧ ε a ≠ ε b then z ⟨(a, b), h⟩
  else if h' : a < b ∧ ε b ≠ ε a then star (z ⟨(b, a), h'⟩) else 0

theorem pmat_isHermitian {ε : Fin n → Bool} (z : PCoord ε → ℂ) : (pmat z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  simp only [pmat]
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · have hn : ¬ (a < b ∧ ε b ≠ ε a) := fun h => absurd h.1 (not_lt.2 h1.1.le)
    simp only [dif_neg hn, dif_pos h1, star_star]
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [dif_pos h2, dif_neg h1]
    · simp only [dif_neg h1, dif_neg h2, star_zero]

def pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) : Fin n → ℝ := (pmat_isHermitian z).eigenvalues

def shc (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u

def Jac {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), shc (pev z a - pev z b)

def Del (A : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℂ :=
  if h : i ≤ n then (A.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def sCoef (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i + 1 < n then lam ⟨i, by omega⟩ - lam ⟨i + 1, h⟩ + 1 else 0

def Fi (X : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ := Real.log (Del (NormedSpace.exp X) i).re

def Ph (lam : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i ∈ range (n - 1), sCoef lam i * Fi X (i + 1)

def Vi (X : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) : ℝ :=
  ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) < i ∧ i ≤ (a : ℕ) then ‖X a b‖ ^ 2 else 0

def wab (lam : Fin n → ℝ) (a b : Fin n) : ℝ := lam b - lam a + ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)

def Qf {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) : ℝ :=
  ∑ ab : PCoord ε, wab lam ab.1.1 ab.1.2 * ‖z ab‖ ^ 2

def rhoP {ε : Fin n → Bool} (z : PCoord ε → ℂ) : ℝ :=
  Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (hs (pmat z))

def PiW (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ := ∏ ab : PCoord ε, Real.pi / wab lam ab.1.1 ab.1.2

def dimVlam (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) /
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

def lamAbs (lam : Fin n → ℝ) : ℝ := ⨆ a : Fin n, ⨆ b : Fin n, |lam a - lam b|

def cPQ (ε : Fin n → Bool) : ℝ :=
  (∏ i ∈ range n, (i.factorial : ℝ)) /
    (Real.pi ^ (pOf ε * qOf ε) * (∏ i ∈ range (pOf ε), (i.factorial : ℝ)) *
      ∏ i ∈ range (qOf ε), (i.factorial : ℝ))

def polarM {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  toMK kz.1 * NormedSpace.exp (pmat kz.2)

def muPolarMat (ε : Fin n → Bool) : Measure (Fin n → Fin n → ℂ) :=
  Measure.map (β := Fin n → Fin n → ℂ) polarM
    ((dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))

def muPolar (ε : Fin n → Bool) : Measure (UJ ε) :=
  Measure.comap (β := Fin n → Fin n → ℂ) (fun g : UJ ε => toM g) (muPolarMat ε)

def muCD (ε : Fin n → Bool) : Measure (Formalism.REAL.UJ ε) :=
  ENNReal.ofReal (cPQ ε) •
    Measure.comap (β := Fin n → Fin n → ℂ) (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) (muPolarMat ε)

def fF (ε : Fin n → Bool) (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ)
    (X : Matrix (Fin n) (Fin n) ℂ) : T.V →L[ℂ] T.V :=
  ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
    ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * X * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)

def hsOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (A : V →L[ℂ] V) : ℝ :=
  ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2

structure FData (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (T : KType ε (lowK ε lam)) (j : T.V →L[ℂ] H) : Prop where
  urep : IsURepOn (UJset ε) σ
  iso : ∀ v, ‖j v‖ = ‖v‖
  kequiv : ∀ (k : KG ε) (v : T.V), σ (toMK k) (j v) = j (T.op k v)
  formF : ∀ z : PCoord ε → ℂ,
    (ContinuousLinearMap.adjoint j).comp ((σ (NormedSpace.exp (pmat z))).comp j) = fF ε lam T (pmat z)

end ReciprocityTheory.ChartRestriction.DS
