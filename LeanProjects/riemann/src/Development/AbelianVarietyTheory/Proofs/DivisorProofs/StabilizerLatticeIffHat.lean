import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

namespace GlobalTheory.KMStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem hat_eq_latHat (L : Set (Fin n → E)) :
    ((hat F L : AddSubgroup (Fin n → RA F E)) : Set (Fin n → RA F E)) = (latHat F E L : Set _) := by
  unfold hat latHat
  congr 2

theorem mem_hat_iff (L : Set (Fin n → E)) (y : Fin n → RA F E) : y ∈ hat F L ↔ y ∈ latHat F E L := by
  have h := hat_eq_latHat (F := F) L
  constructor
  · intro hy; have : y ∈ ((hat F L : AddSubgroup _) : Set _) := hy; rw [h] at this; exact this
  · intro hy; have : y ∈ ((latHat F E L : AddSubgroup _) : Set _) := hy; rw [← h] at this; exact this

theorem isKM_one_iff_stabHat (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E))
    (k : Matrix (Fin n) (Fin n) (RA F E)) (hk : IsUA c G k) :
    IsKM c G L 1 k ↔ GlobalTheory.Mem.Vol.StabHat F L k := by
  have hdet : IsUnit k.det := hk.1
  constructor
  · rintro ⟨-, h2, h3⟩ y
    rw [← mem_hat_iff, ← mem_hat_iff]
    constructor
    · intro hy
      obtain ⟨z, hz, hzk⟩ := h2 y hy
      have : k *ᵥ y = z + y := by rw [one_smul] at hzk; rw [← hzk]; abel
      rw [this]; exact add_mem hz hy
    · intro hy
      obtain ⟨z, hz, hzk⟩ := h3 _ hy
      have hinj : z = y := by
        have e1 : k⁻¹ *ᵥ (k *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
        have e2 : k⁻¹ *ᵥ (k *ᵥ y) = y := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
        rw [← e1, ← e2, hzk]
      rw [← hinj]; exact hz
  · intro hS
    refine ⟨hk, fun x hx => ?_, fun x hx => ?_⟩
    · have hkx : k *ᵥ x ∈ hat F L := (mem_hat_iff L _).2 ((hS x).1 ((mem_hat_iff L x).1 hx))
      exact ⟨k *ᵥ x - x, sub_mem hkx hx, by rw [one_smul]⟩
    · have e : k *ᵥ (k⁻¹ *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      refine ⟨k⁻¹ *ᵥ x, (mem_hat_iff L _).2 ((hS _).2 ?_), e⟩
      rw [e]; exact (mem_hat_iff L x).1 hx

theorem isKM_one_iff_stabHat_of_isSA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E)
    (L : Set (Fin r → E)) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), IsSA G k →
    (IsKM (IsCMField.complexConj E) G L 1 k ↔ GlobalTheory.Mem.Vol.StabHat (maximalRealSubfield E) L k) := by
  intro E _ _ _ r G L k hk
  exact isKM_one_iff_stabHat _ G L k hk.1

end GlobalTheory.KMStab
