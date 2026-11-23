import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDlogUniqueModuloP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_unique_modulo_p : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (O : Type) [CommRing O] (x : Sp O ⟶ X) (p n : ℕ) (c : TorsChar t x (p ^ n)) (g : ℕ) (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∃ h : Fin g → O, DlogIs t p n c e h) ∧ ∀ h h' : Fin g → O, DlogIs t p n c e h → DlogIs t p n c e h' → ∀ i, h i - h' i ∈ Ideal.span {(p : O) ^ n} := by
  first | exact @GlobalTheory.DlogEx.dlog_exists_unique | exact GlobalTheory.DlogEx.dlog_exists_unique | (intros; apply GlobalTheory.DlogEx.dlog_exists_unique <;> assumption)
