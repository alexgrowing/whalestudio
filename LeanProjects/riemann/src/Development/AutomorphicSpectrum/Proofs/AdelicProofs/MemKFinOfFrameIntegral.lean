import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem mem_KFin_of_frame_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (σ : E →ₐ[F] E) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (b : GL (Fin n) (Fv F v ⊗[F] E))
    (hb : ∀ y : Fin n → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v) (k : GLoc σ Q v)
    (h1 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * matHom _ σ Q k * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v)
    (h2 : ∀ i j, ((blkGL finSumFinEquiv (b, b))⁻¹ * (matHom _ σ Q k)⁻¹ * blkGL finSumFinEquiv (b, b)).1 i j ∈ intLoc F E v) :
    k ∈ KFin σ Q L v := by
  have hB : ∀ y : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, y i ∈ intLoc F E v) ↔
      (blkGL finSumFinEquiv (b, b)).1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    intro y
    rw [latLoc_sumLat]
    conv_rhs => rw [← pairVec_eta finSumFinEquiv y]
    rw [val_blkGL, blkMat_mulVec, pairVec_mem_sumLat, ← hb, ← hb]
    constructor
    · exact fun h => ⟨fun i => h _, fun i => h _⟩
    · rintro ⟨h, h'⟩ j
      obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective j
      exacts [h i, h' i]
  have hint : ∀ K : Matrix (Fin (n + n)) (Fin (n + n)) (Fv F v ⊗[F] E), (∀ i j, K i j ∈ intLoc F E v) →
      ∀ z : Fin (n + n) → Fv F v ⊗[F] E, (∀ i, z i ∈ intLoc F E v) → ∀ i, (K *ᵥ z) i ∈ intLoc F E v :=
    fun K hK z hz i => by
      change ∑ j, K i j * z j ∈ _
      exact sum_mem fun j _ => mul_mem (hK i j) (hz j)
  refine mem_stabLoc.2 fun y => ?_
  generalize blkGL finSumFinEquiv (b, b) = B at hB h1 h2
  generalize matHom _ σ Q k = M at h1 h2 ⊢
  have e0 : y = B.1 *ᵥ ((B⁻¹).1 *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have e1 : M.1 *ᵥ y = B.1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have e2 : (B⁻¹).1 *ᵥ y = (B⁻¹ * M⁻¹ * B).1 *ᵥ ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul]
    congr 2
    group
  have hy : y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔ ∀ i, ((B⁻¹).1 *ᵥ y) i ∈ intLoc F E v := by
    rw [hB, ← e0]
  have hMy : M.1 *ᵥ y ∈ latLoc F (sumLat finSumFinEquiv L L) v ↔
      ∀ i, ((B⁻¹ * M * B).1 *ᵥ ((B⁻¹).1 *ᵥ y)) i ∈ intLoc F E v := by
    rw [hB, ← e1]
  rw [hy, hMy]
  refine ⟨hint _ h1 _, fun h => ?_⟩
  rw [e2]
  exact hint _ h2 _ h

end GlobalTheory.CompanionTheory.IwaDbl
