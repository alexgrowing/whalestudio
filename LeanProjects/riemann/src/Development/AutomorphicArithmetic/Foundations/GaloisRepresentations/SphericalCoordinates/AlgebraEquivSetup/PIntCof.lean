import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.VecCoord
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem UpperTheory.Gal.W2.Seed.pIntCof :
    IntCof := by
  intro E _ _ n a
  have key : ∀ x : Af E, ∀ᶠ w : Plc E in Filter.cofinite, pLoc E w x ∈ w.adicCompletionIntegers E :=
    fun x => x.2
  have h1 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key (a.val i j)))
  have h2 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key ((a⁻¹).val i j)))
  filter_upwards [h1, h2] with w ha hb
  refine mem_GLint_of_entries (w.adicCompletionIntegers E).toSubring _ (fun i j => ha i j) (fun i j => ?_)
  rw [← map_inv]
  exact hb i j
