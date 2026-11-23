import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalOfLocalPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteHopfPointsSeparate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLocalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrouplikeOfMultiplicativeFunctionHopfStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_tensor_of_bicharacter : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (A : Type) [CommRing A] [HopfAlgebra R A] [IsCocomm R A] [Module.Finite R A] [Module.Projective R A] (θ : TorsPt G N A), IsLevel K θ → ∀ e : (A →ₐ[R] K) → (A →ₐ[R] K) → K, (∀ x y z w : A →ₐ[R] K, toConv z = toConv x * toConv y → e z w = e x w * e y w ∧ e w z = e w x * e w y) → (∀ x y, e x y ≠ 0) → (∀ (B : Type) [CommRing B] [Algebra R B] (z z' : Tors G N B), ∃ c : B, ∀ ψ : B →ₐ[R] K, ψ c = e (θ.pt K (torsMap ψ z)) (θ.pt K (torsMap ψ z'))) → ∃ T : A ⊗[R] A, ∀ x y : A →ₐ[R] K, Algebra.TensorProduct.lift x y (fun _ _ => .all _ _) T = e x y := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN A _ _ _ _ _ θ hθ e hmul hne hint
  haveI : Finite (A →ₐ[R] K) := (GlobalTheory.HopfPoints.finite_points_separate_rank R K A).1
  haveI : Finite (A ⊗[R] A →ₐ[R] K) := by
    refine Finite.of_injective (fun ψ : A ⊗[R] A →ₐ[R] K =>
      ((ψ.comp Algebra.TensorProduct.includeLeft : A →ₐ[R] K),
        (ψ.comp Algebra.TensorProduct.includeRight : A →ₐ[R] K))) ?_
    intro ψ ψ' h
    exact Algebra.TensorProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  obtain ⟨k, T, hT⟩ := GlobalTheory.AlgPointsLocal.exists_pow_mul_of_locally_integral R K (A ⊗[R] A) 1
    (fun ψ => e (ψ.comp Algebra.TensorProduct.includeLeft) (ψ.comp Algebra.TensorProduct.includeRight)) (by
      intro P _ _
      obtain ⟨z₁, s₁, h₁⟩ := GlobalTheory.T.level_structure_local_points R K G hG N hN A θ hθ (Localization.AtPrime P)
        ((IsScalarTower.toAlgHom R (A ⊗[R] A) (Localization.AtPrime P)).comp Algebra.TensorProduct.includeLeft)
      obtain ⟨z₂, s₂, h₂⟩ := GlobalTheory.T.level_structure_local_points R K G hG N hN A θ hθ (Localization.AtPrime P)
        ((IsScalarTower.toAlgHom R (A ⊗[R] A) (Localization.AtPrime P)).comp Algebra.TensorProduct.includeRight)
      obtain ⟨a₂, ha₂⟩ := GlobalTheory.T.exists_element_of_multiplicative_function_hopf R K A (fun x => e x ((Algebra.ofId R K).comp s₂))
        (fun x y z h => (hmul x y z _ h).1) (fun x => hne _ _)
      obtain ⟨a₁, ha₁⟩ := GlobalTheory.T.exists_element_of_multiplicative_function_hopf R K A (fun x => e ((Algebra.ofId R K).comp s₁) x)
        (fun x y z h => (hmul x y z _ h).2) (fun x => hne _ _)
      obtain ⟨c, hc⟩ := hint (Localization.AtPrime P) z₁ z₂
      have key : ∀ (ψ : Localization.AtPrime P →ₐ[R] K) (φ : A →ₐ[R] Localization.AtPrime P)
          (z : Tors G N (Localization.AtPrime P)) (s : A →ₐ[R] R),
          toConv φ = toConv (θ.pt _ z) * toConv ((Algebra.ofId R _).comp s) →
          toConv (ψ.comp φ) = toConv (θ.pt K (torsMap ψ z)) * toConv ((Algebra.ofId R K).comp s) := by
        intro ψ φ z s h
        have h' := AlgHom.comp_convMul_distrib ψ (toConv (θ.pt _ z)) (toConv ((Algebra.ofId R _).comp s))
        rw [← h, ofConv_toConv, ofConv_toConv, ofConv_toConv, ← θ.nat, ← AlgHom.comp_assoc,
          Subsingleton.elim (ψ.comp (Algebra.ofId R _)) (Algebra.ofId R K)] at h'
        rw [h', toConv_ofConv]
      refine ⟨c * θ.pt _ z₁ a₂ * θ.pt _ z₂ a₁ * algebraMap R _ (s₁ a₂), fun ψ => ?_⟩
      have k₁ := key ψ _ z₁ s₁ h₁
      have k₂ := key ψ _ z₂ s₂ h₂
      show _ = e (ψ.comp ((IsScalarTower.toAlgHom R (A ⊗[R] A) (Localization.AtPrime P)).comp
          Algebra.TensorProduct.includeLeft))
        (ψ.comp ((IsScalarTower.toAlgHom R (A ⊗[R] A) (Localization.AtPrime P)).comp
          Algebra.TensorProduct.includeRight))
      rw [(hmul _ _ _ _ k₁).1, (hmul _ _ _ _ k₂).2, (hmul _ _ _ _ k₂).2, ← hc ψ, ← ha₂, ← ha₁, ← ha₂,
        θ.nat, θ.nat, map_mul, map_mul, map_mul, ψ.commutes, ← _root_.mul_assoc]
      rfl)
  refine ⟨T, fun x y => ?_⟩
  rw [hT, map_one, one_pow, _root_.one_mul]
  congr 1
  · ext a; simp
  · ext a; simp

end GlobalTheory.GroupBplus.Aff
