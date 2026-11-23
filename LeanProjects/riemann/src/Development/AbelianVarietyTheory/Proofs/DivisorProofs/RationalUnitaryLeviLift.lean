import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviRat

open Matrix GlobalTheory.LeviElem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem unitary_map (σ : E →ₐ[F] E) {n : ℕ} (A J : Matrix (Fin n) (Fin n) E) (hA : Aᵀ * J * A.map σ = J) :
    (A.map (inclR (F := F) (AF F)))ᵀ * J.map (inclR (F := F) (AF F)) *
      (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = J.map (inclR (F := F) (AF F)) := by
  have e : (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by
    ext i j; simp [cA, inclR]
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hA]

theorem unitary_of_map (σ : E →ₐ[F] E) {n : ℕ} (A J : Matrix (Fin n) (Fin n) E)
    (hA : (A.map (inclR (F := F) (AF F)))ᵀ * J.map (inclR (F := F) (AF F)) *
      (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = J.map (inclR (F := F) (AF F))) :
    Aᵀ * J * A.map σ = J := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))
  apply Matrix.map_injective hinj
  have e : (A.map (inclR (F := F) (AF F))).map (cA σ).toRingHom = (A.map σ).map (inclR (F := F) (AF F)) := by
    ext i j; simp [cA, inclR]
  rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul] at hA
  exact hA

theorem exists_rat_isLevi_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ γ ∈ ratU σ G₁.V.J, ∃ h ∈ ratU σ G.V.J, IsLevi H 1 γ h := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ γ hγ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  set P := fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * G.V.J * P.map σ = fromBlocks G₁.V.J 0 0 swap2 := gram_block σ hσ B hG.hV.herm hC.hH
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := fromBlocks G₁.V.J 0 0 swap2 with hKdef
  have hKdet : IsUnit Kᵀ.det := by
    rw [det_transpose, hKdef, det_fromBlocks_zero₂₁]
    simp [swap2, det_fin_two, hdet]
  set Q := (Kᵀ)⁻¹ * ((P.map σ)ᵀ * G.V.Jᵀ) with hQ
  have hQP : Q * P = 1 := by
    have : (P.map σ)ᵀ * G.V.Jᵀ * P = Kᵀ := by
      rw [← hK]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hQ, Matrix.mul_assoc, this, nonsing_inv_mul _ hKdet]
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hγ
  have hγm : mat γ = (g : Matrix (Fin b) (Fin b) E).map f := by
    simp only [mat]; rw [← hg]; rfl
  have hγu : (mat γ)ᵀ * incM F G₁.V.J * (mat γ).map (cA σ).toRingHom = incM F G₁.V.J := γ.2
  rw [hγm] at hγu
  have hgu : (g : Matrix (Fin b) (Fin b) E)ᵀ * G₁.V.J * (g : Matrix (Fin b) (Fin b) E).map σ.toRingHom = G₁.V.J :=
    unitary_of_map σ _ _ hγu
  obtain ⟨m₀, hu, hx, hy, hι⟩ := levi_mat σ.toRingHom hσ H.ι H.x H.y G.V.J G₁.V.J Q hQP hK 1 g hgu
  let h : UA σ G.V.J := ⟨Matrix.GeneralLinearGroup.map f m₀, unitary_map σ _ _ hu⟩
  have hmv : ∀ v : Fin (b + 2) → E, mat h *ᵥ incV F v = incV F ((m₀ : Matrix _ _ E) *ᵥ v) :=
    fun v => funext fun i => (RingHom.map_mulVec f _ _ i).symm
  refine ⟨h, Subgroup.mem_subgroupOf.2 ⟨m₀, rfl⟩, ?_, ?_, ?_⟩
  · rw [hmv, hx]; simp
  · rw [hmv, hy]; simp
  · rw [hγm]
    show (m₀ : Matrix _ _ E).map f * H.ι.map f = H.ι.map f * (g : Matrix (Fin b) (Fin b) E).map f
    rw [← Matrix.map_mul, ← hι]
    first | exact Matrix.map_mul.symm | exact (RingHom.map_matrix_mul' f _ _).symm | simp [Matrix.map_mul]

end GlobalTheory.LeviRat

end
