import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatementOfDegreeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.FlatDegreeCompare

theorem UpperTheory.eigen_basis_of_independent_eigenvectors :
    ∀ (K O : Type) [Field K] [CommRing O] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (act : OAct O A) (χ : O →+* K) (m : ℕ) (x v : Fin m → (epsR K ⟶ A)), EigenvectorLieDegree.IsEigBasis act χ x → (∀ i, EigenvectorLieDegree.IsEigVec act χ (v i)) → Indep v → EigenvectorLieDegree.IsEigBasis act χ v := by
  intro K O _ _ A _ _ act χ m x v hx hv hi
  have tx : ∀ i, IsTangent (x i) := fun i => (hx.1 i).1
  choose T hT _ using fun i => hx.2 (v i) (hv i)
  let T' : Matrix (Fin m) (Fin m) K := T
  have hT' : ∀ i, IsLieComb (T' i) x (v i) := hT
  have hinj : Function.Injective (fun c => Matrix.vecMul c T') := fun c c' h =>
    sub_eq_zero.1 (hi.vecMul_eq_zero tx hT' _ (by rw [Matrix.sub_vecMul]; exact sub_eq_zero.2 h))
  have hu : IsUnit T' := Matrix.vecMul_injective_iff_isUnit.1 hinj
  refine ⟨hv, fun w hw => ?_⟩
  obtain ⟨c, hc, -⟩ := hx.2 w hw
  obtain ⟨c, rfl⟩ := Matrix.vecMul_surjective_iff_isUnit.2 hu c
  have h := (comb_comb tx hT' c w).2 hc
  exact ⟨c, h, fun c' h' => hi.2 _ _ w h' h⟩
