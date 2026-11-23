import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BdFib

def fibTorusExtension {k : Type} [Field k] (φ : Fib k) : TorusExtension φ.G where
  X := φ.X
  B := φ.P.A
  isAbelian := φ.P.isAb
  q := φ.q
  q_hom := φ.q_hom
  q_flat := φ.q_flat
  q_surjective := φ.q_surj
  q_quasiCompact := have := φ.q_affine; inferInstance
  i := φ.i
  i_hom := φ.i_hom
  isKernel := φ.isKernel

theorem finrank_eq_of_torRk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ r : ℕ, TorRk t x r → Module.finrank ℤ φ.X = r := by
  intro E _ _ _ H X t k _ x φ m h r hr
  obtain ⟨e, he, -⟩ := grpPullback_iso h.1 (isGrpPullback_pullback t.G x)
  exact hr (torusExtOfIso e (fibTorusExtension φ))

end GlobalTheory.BdFib

end
