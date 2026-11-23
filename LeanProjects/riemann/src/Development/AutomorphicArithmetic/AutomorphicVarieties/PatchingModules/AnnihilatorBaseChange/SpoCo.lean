import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SplittingAlgebraNontrivialFreeGenerated
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ChiRes

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spoCo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → (IsCO O (Spo A) ∧ Module.Free B (Spo A) ∧ Module.Finite B (Spo A) ∧ Algebra.adjoin B (Set.range fun p : Fin T.q × Fin n => (Sp.u _ _ p.1 p.2 : Spo A)) = ⊤) ∧ ∀ N, IsCO O (SpAt u (fun j => (T.h N).p₀ (T.ph N j)) A.ut) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hA
  refine ⟨spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u (T.sg j) (A.ut j) (A.ut_res j), fun N => ?_⟩
  refine (spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u ((T.h N).p₀ (T.ph N j)) (A.ut j) fun i => ?_).1
  have h1 := hA.1 ((T.h N).p₀ (T.ph N j) * (T.sg j)⁻¹) (T.ph_H N j) i
  have h2 := ((r.chib i).map_mul _ _).symm.trans h1
  have h3 := (congrArg (r.chib i ((T.h N).p₀ (T.ph N j)) * ·) ((r.chib i).map_inv (T.sg j))).symm.trans h2
  exact (A.ut_res j i).trans (congrArg Units.val (mul_inv_eq_one.1 h3).symm)
