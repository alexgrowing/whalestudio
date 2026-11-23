import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_flat_locallyQuasiFinite : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ q : ℕ, q ≠ 0 → Flat (torsion G q).hom ∧ LocallyQuasiFinite (torsion G q).hom := by
  first | exact @GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion | exact GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion | (intros; apply GlobalTheory.FibreFlatGen.flat_and_locallyQuasiFinite_torsion <;> assumption)
