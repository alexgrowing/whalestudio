import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions NumberField

namespace GlobalTheory

def trivialIntersectionTheory (d : ℕ) : DV.ITh where
  LB := Unit
  Ch := ℚ
  c1 := fun _ => 0
  VDiv := ℚ
  cD := 0
  capDeg := 0
  divP := 1
  cD_divP := rfl
  dim := d

def trivialFlagPair (d r : ℕ) : DV.FPair (trivialIntersectionTheory d) r where
  x := fun _ => ()
  x' := fun _ => ()
  Dv := fun _ => 0
  hx := fun _ => by
    rw [map_zero, sub_zero]

theorem sub_rkOf_psiOf_eq_rkOf_cEmb (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) (τ : DV.Emb D p) :
    N - DV.rkOf (DV.PsiOf D jc) N j τ = DV.rkOf (DV.PsiOf D jc) N j (DV.cEmb D τ) := by
  have h := Formalism.L2.Geo.cm_type_meets_conjugate_pair p jc τ
  unfold DV.rkOf
  by_cases hτ : τ ∈ DV.PsiOf D jc
  · rw [if_pos hτ, if_neg (h.1 hτ)]
  · have hc : DV.cEmb D τ ∈ DV.PsiOf D jc := by
      by_contra hn
      exact hτ (h.2 hn)
    rw [if_neg hτ, if_pos hc]
    omega

def trivialAdmissibleModel (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ)
    (N j : ℕ) (hj : j ≤ N) : DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j) where
  Z := trivialIntersectionTheory (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
  cov := 1
  cov_pos := Nat.one_pos
  lvl := 0
  lie := fun _ => trivialFlagPair _ _
  om := fun _ => trivialFlagPair _ _
  lieW := trivialFlagPair _ _
  omW := trivialFlagPair _ _
  om_dual := fun τ =>
    ⟨finCongr (sub_rkOf_psiOf_eq_rkOf_cEmb D p jc N j hj τ), fun _ => neg_zero.symm⟩
  dim_eq := rfl
  omW_dual := ⟨Equiv.refl _, fun _ => neg_zero.symm⟩

theorem nonempty_admissibleModel :
    ∀ (D : D7) (p : ℕ) [Fact p.Prime] (jc : DV.KW p →+* ℂ) (N j : ℕ), j ≤ N →
      Nonempty (DV.Mdl D p N (DV.rkOf (DV.PsiOf D jc) N j)) :=
  fun D p _ jc N j hj => ⟨trivialAdmissibleModel D p jc N j hj⟩

end GlobalTheory

end
