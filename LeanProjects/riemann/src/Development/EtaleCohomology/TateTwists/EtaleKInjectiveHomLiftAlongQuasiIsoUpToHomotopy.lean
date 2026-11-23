import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomExtendsAlongQuasiIso

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy : Prop :=
  ∀ (R : Type) [CommRing R] (K L I : Cx R) [I.IsKInjective] (f : K ⟶ L) [QuasiIso f],
    (∀ a : K ⟶ I, ∃ m : L ⟶ I, Nonempty (Homotopy (f ≫ m) a)) ∧
    ∀ m m' : L ⟶ I, Nonempty (Homotopy (f ≫ m) (f ≫ m')) → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (I : Cx R) [I.IsStrictlyGE 0] (a b : sgl F ⟶ I),
    Nonempty (Homotopy a b) → a = b

theorem LateralTheory.EtaleFoundations.etale_sheaf_ext_hom_injective_resolution_of_lift_and_rigidity (hA : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy)
    (hB : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual) : LateralTheory.EtaleFoundations.EtaleKInjectiveHomExtendsAlongQuasiIso := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m, hm⟩ := (hA R (sgl F) T I ε).1 a
    exact ⟨m, hB R F I _ _ hm⟩
  · exact (hA R (sgl F) T I ε).2 m m' ⟨Homotopy.ofEq h⟩
