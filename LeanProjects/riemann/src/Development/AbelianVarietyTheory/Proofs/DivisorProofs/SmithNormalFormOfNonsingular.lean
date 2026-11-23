import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

namespace GlobalTheory.LatChain

theorem mulVec_injective_of_det_ne_zero {R : Type} [CommRing R] [IsDomain R] {N : ℕ}
    (A : Matrix (Fin N) (Fin N) R) (hA : A.det ≠ 0) : Function.Injective A.mulVec := by
  intro x y hxy
  have h := congrArg (fun z => A.adjugate.mulVec z) hxy
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at h
  funext i
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hA this

theorem smith_of_det_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (N : ℕ)
    (A : Matrix (Fin N) (Fin N) R), A.det ≠ 0 → ∃ (u v u' v' : Matrix (Fin N) (Fin N) R) (g : Fin N → R),
      u * v = 1 ∧ u' * v' = 1 ∧ A = u * Matrix.diagonal g * u' := by
  intro R _ _ _ N A hA
  let f : (Fin N → R) →ₗ[R] (Fin N → R) := Matrix.toLin' A
  have hinj : Function.Injective f := by
    intro x y h
    exact mulVec_injective_of_det_ne_zero A hA (by simpa [f, Matrix.toLin'_apply] using h)
  let e : (Fin N → R) ≃ₗ[R] LinearMap.range f := LinearEquiv.ofInjective f hinj
  let std := Pi.basisFun R (Fin N)
  let bN : Module.Basis (Fin N) R (LinearMap.range f) := std.map e
  have hrk : Module.finrank R (LinearMap.range f) = Module.finrank R (Fin N → R) := by
    rw [Module.finrank_eq_card_basis bN, Module.finrank_eq_card_basis std]
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq std hrk
  let w : Module.Basis (Fin N) R (Fin N → R) := ab'.map e.symm
  have hw : ∀ j, A.mulVec (w j) = a j • b' j := by
    intro j
    have h1 : f (w j) = (ab' j : Fin N → R) := by
      simp only [w, Module.Basis.map_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (ab' j))
    rw [← hab j, ← h1]
    simp [f, Matrix.toLin'_apply]
  let Q := std.toMatrix w
  let P := std.toMatrix b'
  have hQV : Q * w.toMatrix std = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std w
  have hVQ : w.toMatrix std * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w std
  have hPW : P * b'.toMatrix std = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b'
  have hMQ : A * Q = P * Matrix.diagonal a := by
    ext i j
    have h1 := congrFun (hw j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h1]; ring
  refine ⟨P, b'.toMatrix std, w.toMatrix std, Q, a, hPW, hVQ, ?_⟩
  calc A = A * (Q * w.toMatrix std) := by rw [hQV, Matrix.mul_one]
    _ = (A * Q) * w.toMatrix std := by rw [Matrix.mul_assoc]
    _ = P * Matrix.diagonal a * w.toMatrix std := by rw [hMQ]

end GlobalTheory.LatChain

end
