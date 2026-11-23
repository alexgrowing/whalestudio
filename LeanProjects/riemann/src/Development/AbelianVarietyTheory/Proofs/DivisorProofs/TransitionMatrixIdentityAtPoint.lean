import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase

theorem evalPt_trCo_self : ∀ {X : Scheme.{0}} {M : X.Modules} {r : ℕ} {U : X.Opens} {f : Fin r → Γ(M, U)} (hf : VB.IsFrame f) {K : Type} [CommRing K] (x : Sp K ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U)) (c a : Fin r), TangentOrigin.evalPt x _ h (trCo hf f c a) = if c = a then 1 else 0 := by
  intro X M r U f hf K _ x h c a
  have e : trCo hf f c a = if c = a then 1 else 0 := by
    unfold trCo
    have : Twist.resM M (inf_le_right : U ⊓ U ≤ U) (f a) = (hf.basis (inf_le_left : U ⊓ U ≤ U)) a := by
      rw [VB.IsFrame.basis_apply]
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [eq_comm]
  rw [e]
  split_ifs
  · exact map_one _
  · exact map_zero _

end GlobalTheory.ArLieBase
