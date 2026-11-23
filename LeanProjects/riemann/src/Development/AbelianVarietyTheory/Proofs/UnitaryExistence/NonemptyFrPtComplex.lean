import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem nonempty_frPt_complex : N1c → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, Nonempty (FrPt Xo c (CAt σ)) := by
  intro hN hT E _ _ _ H Dw l Xo c h σ
  classical
  obtain ⟨L, _, _, j, x, hx⟩ := GlobalTheory.T.xoNumPt_of_p_add_q_pos hN E H Dw l Xo c h
  let _ : Algebra c.F L := j.toAlgebra
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic c.F L := by
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := IsAlgClosed.lift
  let _ : Algebra L ℂ := φ.toRingHom.toAlgebra
  obtain ⟨_, y, _⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := L) (L' := ℂ) hT
    (fun r => (φ.commutes r).symm) x hx (fun τ i j => if i = j then 1 else 0)
    (fun τ i => by simp) (fun τ i j hij => by simp [hij.ne'])
  exact ⟨y⟩

end GlobalTheory
