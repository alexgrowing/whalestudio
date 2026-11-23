import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_elem_of_natural_family_openCoverPoints : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D) (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E), (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), Sm W (spOver ψ ≫ y) → τ E' (θ.comp ψ) = θ (τ E ψ)) → ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (spOver ψ ≫ y) → τ E ψ = ψ d := by
  first | exact @GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | exact GlobalTheory.PtExt.NatGlue.existsUnique_of_natural | (intros; apply GlobalTheory.PtExt.NatGlue.existsUnique_of_natural <;> assumption)
