import Mathlib
open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_eq_map_of_spanning_lattice (R F A S : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] [Algebra R F] [IsFractionRing R F] [CommRing A]
    [Algebra F A] [Algebra R A] [IsScalarTower R F A] [Module.Finite F A] [CommRing S]
    [Algebra R S] [Module.Finite R S] (ι : S →ₐ[R] A) (hι : Function.Injective ι)
    (hspan : Submodule.span F (Set.range ι) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) R S), ∀ x : S, (LinearMap.mulLeft F (ι x)).charpoly =
      ((LinearMap.toMatrix b b (LinearMap.mulLeft R x)).charpoly).map (algebraMap R F) := by
  classical
  have hRF : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  haveI : Module.IsTorsionFree R S := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r x h
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      apply hι
      have h1 : algebraMap R F r • ι x = 0 := by
        rw [algebraMap_smul, ← map_smul, h, map_zero]
      have h2 : algebraMap R F r ≠ 0 := fun h0 => hr (hRF (by simpa using h0))
      rw [map_zero]
      exact (smul_eq_zero.mp h1).resolve_left h2
  haveI : Module.Free R S := Module.free_of_finite_type_torsion_free'
  let b : Module.Basis (Fin (Module.finrank R S)) R S := Module.finBasis R S
  refine ⟨_, b, fun x => ?_⟩
  have hexp : ∀ y : S, ι y = ∑ i, algebraMap R F (b.repr y i) • ι (b i) := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, map_smul, algebraMap_smul]
  have hliR : LinearIndependent R (fun i => ι (b i)) :=
    b.linearIndependent.map' ι.toLinearMap (LinearMap.ker_eq_bot.mpr hι)
  have hli : LinearIndependent F (fun i => ι (b i)) :=
    (LinearIndependent.iff_fractionRing R F).mp hliR
  have hsp : ⊤ ≤ Submodule.span F (Set.range (fun i => ι (b i))) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [hexp y]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b' : Module.Basis (Fin (Module.finrank R S)) F A := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = ι (b i) := fun i => by simp [b']
  have hM : LinearMap.toMatrix b' b' (LinearMap.mulLeft F (ι x)) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft R x)).map (algebraMap R F) := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hb', ← map_mul, hexp]
    simp only [← hb']
    rw [b'.repr_sum_self]
  rw [← LinearMap.charpoly_toMatrix _ b', hM, Matrix.charpoly_map]

end GlobalTheory
