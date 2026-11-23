import Mathlib
import GroundTheory.AutomorphicForms.SphericalIntegral

open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

abbrev Pos : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Res (t : ℕ) : Type := 𝒪[F] ⧸ Ideal.span {uniformizer F ^ t}

abbrev HData (l : Fin n → ℕ) : Type := ∀ p : Pos n, Res F (l p.1.1)

variable {F n}

noncomputable def hnfMat (l : Fin n → ℕ) (a : HData F n l) : Matrix (Fin n) (Fin n) 𝒪[F] :=
  Matrix.of fun i j => if i = j then uniformizer F ^ l i
    else if h : i < j then Quotient.out (a ⟨(i, j), h⟩) else 0

theorem hnfMat_diag (l : Fin n → ℕ) (a : HData F n l) (i : Fin n) :
    hnfMat l a i i = uniformizer F ^ l i := by
  simp [hnfMat]

theorem hnfMat_of_gt (l : Fin n → ℕ) (a : HData F n l) {i j : Fin n} (h : j < i) :
    hnfMat l a i j = 0 := by
  simp [hnfMat, h.ne', not_lt.2 h.le]

noncomputable def hnfF (l : Fin n → ℕ) (a : HData F n l) : Matrix (Fin n) (Fin n) F :=
  (hnfMat l a).map (fun x => (x : F))

theorem det_hnfF (l : Fin n → ℕ) (a : HData F n l) :
    (hnfF l a).det = ∏ i, (uniformizer F : F) ^ l i := by
  rw [Matrix.det_of_upperTriangular]
  · simp [hnfF, hnfMat_diag]
  · intro i j h
    simp [hnfF, hnfMat_of_gt l a (show j < i from h)]

theorem det_hnfF_ne_zero (l : Fin n → ℕ) (a : HData F n l) : (hnfF l a).det ≠ 0 := by
  rw [det_hnfF]
  exact Finset.prod_ne_zero_iff.2 fun i _ =>
    pow_ne_zero _ fun h => (irreducible_uniformizer F).ne_zero (Subtype.ext h)

noncomputable def hnfGL (l : Fin n → ℕ) (a : HData F n l) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hnfF l a) (det_hnfF_ne_zero l a)

variable (F n) in

def intCosets (k : ℕ) : Set (GL (Fin n) F ⧸ integralGL F n) :=
  {c | (∀ i j, c.out.val i j ∈ (ValuativeRel.valuation F).integer) ∧
    ValuativeRel.valuation F c.out.val.det = ValuativeRel.valuation F (uniformizer F : F) ^ k}

variable (F n) in

abbrev HDataDeg (k : ℕ) : Type := Σ l : {l : Fin n → ℕ // ∑ i, l i = k}, HData F n l.1

noncomputable def hnfCoset {k : ℕ} (s : HDataDeg F n k) : GL (Fin n) F ⧸ integralGL F n :=
  QuotientGroup.mk (hnfGL s.1.1 s.2)

section Basic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

end Basic

end GlobalTheory.HermCount
