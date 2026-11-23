import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedUnique

theorem exists_pM_of_low_zero {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k)
    (hg : g.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), g = pM a d b := by
  have hgb : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ := by
    rw [← hg, fromBlocks_toBlocks]
  have hdet : g.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [hgb, det_fromBlocks_zero₂₁] at hdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), g.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hgb

theorem low_inv_mul_pM {R : Type} [CommRing R] {n : ℕ} (a₁ d₁ a₂ d₂ : GL (Fin n) R)
    (b₁ b₂ : Matrix (Fin n) (Fin n) R) :
    (((pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ : GL (Ix n) R)).1.toBlocks₂₁ = 0 := by
  have h1 : ((pM a₁ d₁ b₁ : GL (Ix n) R)).1 = fromBlocks a₁.1 b₁ 0 d₁.1 := rfl
  have h2 : (((pM a₂ d₂ b₂)⁻¹ : GL (Ix n) R)).1 =
      fromBlocks (a₂⁻¹).1 (-((a₂⁻¹).1 * b₂ * (d₂⁻¹).1)) 0 (d₂⁻¹).1 := rfl
  rw [Units.val_mul, h1, h2, fromBlocks_multiply]
  simp [toBlocks_fromBlocks₂₁]

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  intro O L _ _ _ _ _ _ n w κ h₁ h₂ r₁ r₂
  obtain ⟨a₁, d₁, b₁, κ₁, e₁, rfl⟩ := r₁
  obtain ⟨a₂, d₂, b₂, κ₂, e₂, rfl⟩ := r₂
  obtain ⟨c, hcd⟩ : ∃ c : GL (Ix n) O, c = κ₂ * κ₁⁻¹ := ⟨_, rfl⟩
  have hc : inL (L := L) c = (pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ := by
    have e : pM a₁ d₁ b₁ * inL (L := L) κ₁ = pM a₂ d₂ b₂ * inL (L := L) κ₂ := e₁.symm.trans e₂
    rw [hcd, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hlow : (inL (L := L) c).1.toBlocks₂₁ = 0 := by
    rw [hc]; exact low_inv_mul_pM _ _ _ _ _ _
  have hO : ∀ i j, c.1 (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h0 : algebraMap O L (c.1 (Sum.inr i) (Sum.inl j)) = 0 := congrFun (congrFun hlow i) j
    exact IsFractionRing.injective O L (h0.trans (map_zero _).symm)
  have hk : (resK c).1.toBlocks₂₁ = 0 := by
    ext i j
    change IsLocalRing.residue O (c.1 (Sum.inr i) (Sum.inl j)) = 0
    rw [hO, map_zero]
  obtain ⟨a, d, b, hp⟩ := exists_pM_of_low_zero _ hk
  refine ⟨a, d, b, ?_⟩
  rw [← hp, ← map_mul, hcd, inv_mul_cancel_right]

end GlobalTheory.CompanionTheory.Jp.RedUnique

end
