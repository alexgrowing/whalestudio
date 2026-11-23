import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeComplexPrimitiveLineBundleCechFibres
import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPerfectFreeFiniteComplex
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_free_complex_primitive_lineBundle_cech_fibres : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ g : ℕ, SmoothOfRelativeDimension g B.hom → ∀ F : LB B.left, F.IsLB → (∃ u : LB.Gen (abelian₂ B F), u.IsGen) → ∀ P : Perf B.hom F, ∃ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) ∧ (∃ n, ∀ i, n < i → IsZero (C.X i)) ∧ Nonempty ((Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] ((Fin P.a → A) ⧸ LinearMap.range P.D₀.transpose.mulVecLin)) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ i, (g < i ∨ ¬ Triv (F.pull π)) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) ∧ ∀ (K : Type) [Field K] (φ : A →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom φ)) → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X'.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ i, Nonempty ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).homology i ≃ₗ[K] (cechLB f' (F.pull π) D).homology i) := by
  first | exact @GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | exact GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech | (intros; apply GlobalTheory.AbLaw.exists_free_complex_of_primitive_cech <;> assumption)
