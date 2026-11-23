import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory.LeftBasisBC

theorem existsUnique_coords_baseChange (K : Type) [CommRing K] [Algebra ℚ K]
    (L : Type) [Field L] [Algebra ℚ L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C) (h : ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i)
    (y : K ⊗[ℚ] C) :
    ∃! β : Fin r → K ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (β i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
  let φ : (Fin r → L) →ₗ[ℚ] C :=
    { toFun := fun c => ∑ i, ι (c i) * e i
      map_add' := fun a b => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun q a => by simp [Finset.smul_sum] }
  have hφ : Function.Bijective φ := by
    rw [Function.bijective_iff_existsUnique]
    intro x
    obtain ⟨c, hc, hu⟩ := h x
    exact ⟨c, hc.symm, fun d hd => hu d hd.symm⟩
  let E : (Fin r → L) ≃ₗ[ℚ] C := LinearEquiv.ofBijective φ hφ
  let P : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] (Fin r → K ⊗[ℚ] L) :=
    TensorProduct.piRight ℚ ℚ K (fun _ : Fin r => L)
  let F : K ⊗[ℚ] (Fin r → L) ≃ₗ[ℚ] K ⊗[ℚ] C := TensorProduct.congr (LinearEquiv.refl ℚ K) E
  have key : ∀ z : K ⊗[ℚ] (Fin r → L), F z =
      ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ K) ι (P z i) * ((1 : K) ⊗ₜ[ℚ] e i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp [F, P, E, φ, TensorProduct.tmul_sum]
    | add a b ha hb =>
      simp only [map_add, ha, hb, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  refine ⟨P (F.symm y), ?_, ?_⟩
  · show y = _
    rw [← key, LinearEquiv.apply_symm_apply]
  · intro β hβ
    have h1 := key (P.symm β)
    rw [LinearEquiv.apply_symm_apply, ← hβ] at h1
    rw [← h1, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem existsUnique_coords_adicCompletion :
    ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) :=
  fun L _ _ C _ _ ι r e h v y =>
    existsUnique_coords_baseChange (v.adicCompletion ℚ) L C ι r e h y

end GlobalTheory.LeftBasisBC
