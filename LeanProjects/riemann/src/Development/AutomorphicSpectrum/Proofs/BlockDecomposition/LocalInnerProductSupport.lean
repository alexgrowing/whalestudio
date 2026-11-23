import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem entries_iff (h : GL (Fin 2) F) (l : Fin 3 → ℤ) (x : Fin 2 → F) :
    (∀ i j, ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j ∈ 𝒪[F]) ↔
    (∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) ∧
    ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F] := by
  simp only [Units.val_mul, coe_torusPow, Matrix.mul_diagonal, Fin.forall_fin_succ, Fin.forall_fin_two,
    Ad3.LFS.blk]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.diagonal_apply]
  have e : ∀ a b c d t : F, t * a * b + t * c * d = (a * b + c * d) * t := fun a b c d t => by ring
  simp only [e]
  tauto

end

theorem innred : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  intro F _ _ _ _ _ _ ψ h l
  have h1 : ∀ X : Matrix (Fin 2) (Fin 3) F, (∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 1 := fun X hX =>
    Set.indicator_of_mem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  have h0 : ∀ X : Matrix (Fin 2) (Fin 3) F, (¬ ∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 0 := fun X hX =>
    Set.indicator_of_notMem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  refine ⟨fun hn => ?_, fun hy => ?_⟩
  · unfold Ad3.LFS.inn
    have hz : ∀ x : Fin 2 → F, Ad3.LFS.Φ0 F ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 0 := fun x =>
      h0 _ fun q => hn ((entries_iff h l x).1 q).1
    simp [hz]
  · unfold Ad3.LFS.inn
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]
    · beta_reduce
      rw [h1 _ ((entries_iff h l x).2 ⟨hy, hx⟩), one_mul]
      exact (Set.indicator_of_mem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm
    · beta_reduce
      rw [h0 _ fun q => hx ((entries_iff h l x).1 q).2, zero_mul]
      exact (Set.indicator_of_notMem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm

end GlobalTheory.CompanionTheory.LFUDom
