import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

namespace GlobalTheory.IndLineGL

open GlobalTheory.SmGL GlobalTheory.PRep
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

scoped instance vrelFv {F : Type} [Field F] [NumberField F] (v : Pl F) : ValuativeRel (Fv F v) := GlobalTheory.LocalData.complRel v

scoped instance locFieldFv {F : Type} [Field F] [NumberField F] (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) :=
  GlobalTheory.LocalData.isLocalField v

abbrev blk3 (m : ℕ) : Fin 3 → ℕ := ![1, m, 1]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure IsGLIndMap {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) {P P₁ : Type} [AddCommGroup P]
    [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ) (A : P →ₗ[ℂ] (GL (Fin n) k → P₁)) : Prop where
  right : ∀ g x h, A (π g x) h = A x (h * g)
  unip : ∀ u ∈ unipRad k e, ∀ x h, A x (u * h) = A x h
  levi : ∀ (l : Levi k (fun i : Fin 3 => Fin (blk3 m i))) x h, A x (leviEmb k e l * h) =
    ((ξ₁ (Matrix.GeneralLinearGroup.det (l 0)) * ξ₂ (Matrix.GeneralLinearGroup.det (l 2)) : ℂˣ) : ℂ) • σ₁ (l 1) (A x h)

end GlobalTheory.IndLineGL
