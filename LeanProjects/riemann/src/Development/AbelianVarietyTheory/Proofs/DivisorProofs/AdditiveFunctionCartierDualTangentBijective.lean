import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDiv

theorem mem_ker_cobOne_of_mul {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] {a : A}
    (h : ∀ φ ψ : CartierDual R A, (φ * ψ) a = φ 1 * ψ a + ψ 1 * φ a) :
    a ∈ LinearMap.ker (cobOne R A) := by
  have hp : IsPrimitiveElem R a := (CartierDual.isPrimitiveElem_iff_mul a).2 h
  rw [LinearMap.mem_ker, cobOne_apply, sub_sub, sub_eq_zero]
  exact hp

theorem primTangent_bijective {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    Function.Bijective (primTangent R A) := by
  constructor
  · intro b b' hbb
    refine Subtype.ext (CartierDual.eq_of_forall_apply (R := R) fun φ => ?_)
    rw [← primTangent_d b φ, ← primTangent_d b' φ, hbb]
  · intro l
    let δ : CartierDual R A →ₗ[R] R := l ∘ₗ AugCot.d (counitAlgHom R (CartierDual R A))
    obtain ⟨a, ha⟩ := (CartierDual.toBidual_bijective (R := R) (M := A)).2 (toConv δ)
    have hδ : ∀ φ : CartierDual R A, φ a = δ φ := fun φ => by
      have := congrArg (fun x => x φ) ha
      simpa using this
    have hmem : a ∈ LinearMap.ker (cobOne R A) := mem_ker_cobOne_of_mul fun φ ψ => by
      rw [hδ, hδ, hδ]
      simp only [δ, LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, smul_eq_mul]
      rfl
    refine ⟨⟨a, hmem⟩, AugCot.hom_ext fun φ => ?_⟩
    rw [primTangent_d]
    exact hδ φ

end PDiv

end GlobalTheory
