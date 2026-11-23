import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeExtensionOverCodimOnePoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_extension_over_codim_one_points : ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] [IsIntegral X], IsSmoothProjCurve k X → ∀ (O : Type) [CommRing O] (A B A' B' : X.Modules) (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r a b a' b' : ℕ), IsVB A a → IsVB B b → IsVB A' a' → IsVB B' b' → ∀ (U : X.Opens), genericPoint X ∈ U → ∀ d₀ : DatumOn α β α' β' r U.ι, HasLatticesDvr d₀ → ∀ x : X, x ∉ U → ∃ V : X.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧ ∃ d : DatumOn α β α' β' r V.ι, ∃ ψ, Agree (b := X.homOfLE (inf_le_left : V ⊓ U ≤ V)) (c := X.homOfLE (inf_le_right : V ⊓ U ≤ U)) d d₀ (by simp) ψ := by
  first | exact @GlobalTheory.LatticeExt.exists_extension | exact GlobalTheory.LatticeExt.exists_extension | (intros; apply GlobalTheory.LatticeExt.exists_extension <;> assumption)
