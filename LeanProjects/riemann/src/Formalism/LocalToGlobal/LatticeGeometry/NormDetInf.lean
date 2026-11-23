import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2.Geo

structure CxPkg (Tau : Type) [Fintype Tau] (N j : ℕ) (Comp : Type) [Fintype Comp] where

  Γ : Comp → Subgroup (Tau → GL (Fin j ⊕ Fin (N - j)) ℂ)
  Γ_le : ∀ c, Γ c ≤ Formalism.DegreeFormula.UpqI Tau j (N - j)

  volC : Comp → ℝ
  volC_pos : ∀ c, 0 < volC c

  rfn : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  rfn_ge : ∀ z, Real.exp 1 ≤ rfn z

  hLo : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hUp : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  hLo_le : ∀ z, 0 < hLo z ∧ hLo z ≤ hUp z

  connN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ
  curvN : (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

  normDetInf : Tau → (Σ c, XCc Tau j (N - j) (Γ c)) → ℝ

namespace CxPkg

variable {Tau : Type} [Fintype Tau] {N j : ℕ} {Comp : Type} [Fintype Comp] (X : CxPkg Tau N j Comp)

def XC : Type := Σ c, XCc Tau j (N - j) (X.Γ c)

def compOf : X.XC → Comp := Sigma.fst

def vol : ℝ := ∑ c, X.volC c

theorem vol_pos [Nonempty Comp] : 0 < X.vol :=
  Finset.sum_pos (fun c _ => X.volC_pos c) Finset.univ_nonempty

def chern : MvPolynomial (DV.Rt Tau N) ℝ →ₗ[ℝ] ℝ := chernOf Tau N X.vol

end CxPkg

end Formalism.L2.Geo
