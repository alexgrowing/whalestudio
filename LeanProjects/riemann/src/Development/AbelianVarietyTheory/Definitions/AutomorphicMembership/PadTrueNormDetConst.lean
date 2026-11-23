import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (Φ : s.Flag)
  {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (Φ.C k) C)
  (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ))
  (hj : ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) (hA : AdmEx S κ) {ng : NgPkg}

def padTrue (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl) : PadPkg D N j s.Comp jC ng :=
  padAt s L G (admissible_representation_factorisation S κ jC hj hA) (flatSt s Φ hm) (arIn s Φ hm)

variable (L : LocSt D N j ng) (G : GlobSt fun p => (L.loc p).Mdl)

theorem padTrue_arDeg : (padTrue s Φ hm jC hj hA L G).arDeg = (arIn s Φ hm).arDeg := rfl

section Prime

open PadPkg (md)

variable {p : ℕ} [Fact p.Prime] {la : PlL D p}

def padTrue_mp (p : ℕ) [Fact p.Prime] (la : PlL D p) :
    (padTrue s Φ hm jC hj hA L G).Mp p la ≃ AdmPl S κ jC hj p la :=
  mpEquiv s L G (admissible_representation_factorisation S κ jC hj hA) (flatSt s Φ hm) (arIn s Φ hm) p la

def padTrue_crv (z : (padTrue s Φ hm jC hj hA L G).Mp p la) :
    (padTrue s Φ hm jC hj hA L G).CurveM p la z ≃ Crv (padTrue_mp s Φ hm jC hj hA L G p la z) where
  toFun c := c.2
  invFun c := ⟨Fact.out, c⟩
  left_inv _ := rfl
  right_inv _ := rfl

example (z : (padTrue s Φ hm jC hj hA L G).Mp p la) :
    (md (padTrue s Φ hm jC hj hA L G) p la z).Z.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1 := rfl

end Prime

example (T : Finset ℕ) (R : ℝ) (x : DV.Rt D.what₂.Tau N) :
    (padTrue s Φ hm jC hj hA L G).arDeg T R (MvPolynomial.X x ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)) =
      ∑ k, polar (fun w => (adlOf (Φ.C k) (hm k) w).arTop) (Multiset.replicate (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1)
        (rootSym S.Dw (ArIn.ind T) (some R) (DV.tauEmb D x.1) x.2)) := by
  rw [padTrue_arDeg, ArIn.arDeg, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  change numL _ _ (MvPolynomial.rename _ _) = _
  rw [map_pow, MvPolynomial.rename_X, numL_X_pow]
  rfl

example (T : Finset ℕ) (R : ℝ) : (padTrue s Φ hm jC hj hA L G).arDeg T R 1 = 0 :=
  (arIn s Φ hm).arDeg_homog T R 1 0 (Nat.succ_ne_zero _).symm (MvPolynomial.isHomogeneous_one _ _)

end GlobalTheory.ShFam.Pad
