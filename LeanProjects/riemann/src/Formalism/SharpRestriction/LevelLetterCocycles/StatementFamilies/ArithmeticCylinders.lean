import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.ArithmeticCylinders

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

variable {D : D7}

def TieCount (A : AllRows D) (n₀ : ℕ) (Alev C₃ cb : ℝ) : Prop :=
  ∃ b h : ℝ,
    (∀ (k : Fin 2) (S : Set (Tup D k)),
      Formalism.MainNotions.PlaceDegreeData.HidaSetting A.B.I n₀ Alev b A.B.lam A.B.μf A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) ∧
      Formalism.MainNotions.PlaceDegreeData.CountData A.B.I A.B.lam A.B.σ A.B.w A.B.σs A.B.tens A.B.μf A.B.fund A.B.R
        (A.eT (cyl D k S)) (A.ReT (cyl D k S))) ∧
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (A.B.I.ε v) (A.B.lam v) h) ∧
    C₃ * (A.B.I.n : ℝ) ^ 19 * (A.B.I.f : ℝ) ^ 5 * Real.log (b * A.B.I.rd) ≤ h ∧
    Real.log (A.B.I.f : ℝ) ≤ Real.sqrt (A.B.I.n : ℝ) ∧
    Real.log (Real.log b) ≤ cb * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ) ∧
    0 < A.B.I.Dstar (Formalism.MainNotions.PlaceDegreeData.fdegAll A.B.I A.B.σ A.B.w) A.B.μf A.B.fund A.B.e

variable (D)

def adm1 (n₀ : ℕ) (Alev C₃ c₃ cb : ℝ) : Prop := Formalism.MainNotions.PlaceDegreeData.PointsLemma D n₀ Alev C₃ c₃ cb

def Adm2 (A : AllRows D) (n₀ : ℕ) (Alev C₃ c₃ cb CL : ℝ) : Prop :=
  adm1 D n₀ Alev C₃ c₃ cb ∧ PlaceLawIdempotents A CL ∧ DimEqTotalCount A ∧ DimEqGoodCount A ∧ LabelCountGoodInjective A ∧ TieCount A n₀ Alev C₃ cb ∧ TieAdmG D

def Conclusion2Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) C c (o x)

def FamilyExpDeficitBound' {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ExpDeficitBound (Fm.D x i) x Fm.ez

def ParO {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2),
    ((Fm.D x i).R.r : ℝ) ^ 2 ≤ δ * ((Fm.D x i).host.g k : ℝ)

def ParX {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ (C c : ℝ) (o : ℝ → ℝ), 0 < c → Tendsto o atTop (𝓝 0) →
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, C * br2 (Fm.D x i) c (o x) ≤ Real.exp (-(x ^ (Fm.ez / 7)))

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : ∀ x (i : Fm.Ix x), AllRows (Fm.D x i)) : Prop :=
  (∀ (c₀ c₂ c₁ : ℝ) (x : ℝ) (i : Fm.Ix x), Stmt (Fm.D x i) c₀ c₂ c₁) ∧
  ∀ (n₀ : ℕ) (Alev C₃ c₃ cb CL x₂ : ℝ), 0 < c₃ →
    (∀ x ≥ x₂, ∀ i : Fm.Ix x, Adm2 (Fm.D x i) (A x i) n₀ Alev C₃ c₃ cb CL) → ParO Fm →
      Conclusion2Family Fm ∧ (ParX Fm → FamilyExpDeficitBound' Fm)

def FamilyLocalShareBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (eV : ∀ x (i : Fm.Ix x), VecAt (Fm.D x i)) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∃ o : ℝ → ℝ, Tendsto o atTop (𝓝 0) ∧
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LocalShareBound (Fm.D x i) (eV x i) C c (o x)

def FamilyLocalShareExpBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (eV : ∀ x (i : Fm.Ix x), VecAt (Fm.D x i)) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, LocalShareExpBound (Fm.D x i) (eV x i) x Fm.ez

def FamilyLocalShareBoundsOfLocalLaw {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (eV : ∀ x (i : Fm.Ix x), VecAt (Fm.D x i)) : Prop :=
  ∀ CL x₂ : ℝ,
    (∀ x ≥ x₂, ∀ i : Fm.Ix x, lawL (Fm.D x i) (eV x i) CL ∧ TieAdmG (Fm.D x i)) → ParO Fm →
      FamilyLocalShareBound Fm eV ∧ (ParX Fm → FamilyLocalShareExpBound Fm eV)

end Formalism.MainNotions.ArithmeticCylinders
