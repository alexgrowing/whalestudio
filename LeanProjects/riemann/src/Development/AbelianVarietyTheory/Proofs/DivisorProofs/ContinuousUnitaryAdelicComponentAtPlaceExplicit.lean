import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem continuous_tensorMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [Algebra ℚ R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
    letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
    Continuous (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsModuleTopology R' (R' ⊗[ℚ] C) := ⟨rfl⟩
  haveI : ContinuousAdd (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousAdd R' _
  haveI : ContinuousSMul R' (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousSMul R' _
  let b := Module.finBasis ℚ C
  let bA := Algebra.TensorProduct.basis R b
  let bB := Algebra.TensorProduct.basis R' b
  have key : ∀ x, Algebra.TensorProduct.map f (AlgHom.id ℚ C) x = ∑ i, f (bA.repr x i) • bB i := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bA, bB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id ℚ C))) = fun x => ∑ i, f (bA.repr x i) • bB i := funext key
  rw [e]
  refine continuous_finset_sum _ fun i _ => ?_
  exact (hf.comp (IsModuleTopology.continuous_of_linearMap (bA.coord i))).smul continuous_const

theorem continuous_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  intro p _ G v
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) _
  have hf : Continuous (AfP.eval v) := RestrictedProduct.continuous_eval v
  have hφ := continuous_tensorMap (C := G.C) (AfP.eval v) hf
  have h1 := Units.continuous_map (f := (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom) hφ
  have h2 := Units.continuous_map (f := (AfP.eval v).toRingHom.toMonoidHom) hf
  refine continuous_induced_rng.2 ?_
  exact (h1.comp (continuous_fst.comp continuous_subtype_val)).prodMk (h2.comp (continuous_snd.comp continuous_subtype_val))

end GlobalTheory.OrbFinAf
