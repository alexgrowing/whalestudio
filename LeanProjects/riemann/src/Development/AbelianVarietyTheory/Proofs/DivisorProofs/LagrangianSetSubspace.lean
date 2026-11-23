import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

noncomputable section
namespace GlobalTheory.ArchSchB

variable {F : Type} [Field F] [NumberField F]

theorem sub_evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + b.1) = _
  exact map_add _ _ _

theorem sub_evI_realAd_mul (t : ℝ) (a : AF F) : evI F (realAd F t * a) = t • evI F a := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * a.1) = _
  rw [map_mul, RingEquiv.apply_symm_apply, Algebra.smul_def]
  rfl

theorem sub_arch_add {κ : Type} (p q : κ → AF F) : arch F (p + q) = arch F p + arch F q := by
  funext i; simp [arch, sub_evI_add]

theorem sub_arch_smul {κ : Type} (t : ℝ) (p : κ → AF F) : arch F (realAd F t • p) = t • arch F p := by
  funext i; simp [arch, sub_evI_realAd_mul]

theorem sub_at_zero {M : Type} [AddCommGroup M] [Module (AF F) M] : At (evI F) (0 : M) :=
  fun u _ => smul_zero u

theorem sub_at_add {M : Type} [AddCommGroup M] [Module (AF F) M] {x y : M} (hx : At (evI F) x)
    (hy : At (evI F) y) : At (evI F) (x + y) :=
  fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

theorem sub_at_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (c : AF F) (hx : At (evI F) x) :
    At (evI F) (c • x) :=
  fun u hu => by rw [smul_comm, hx u hu, smul_zero]

end GlobalTheory.ArchSchB

namespace GlobalTheory.ArchSchB

theorem lagSetB_isSubspace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    (0 ∈ lagSetB M M₁ H H') ∧ (∀ l ∈ lagSetB M M₁ H H', ∀ l' ∈ lagSetB M M₁ H H', l + l' ∈ lagSetB M M₁ H H') ∧
    ∀ t : ℝ, ∀ l ∈ lagSetB M M₁ H H', t • l ∈ lagSetB M M₁ H H' := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ M M₁ H H'
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, 0, 0, sub_at_zero, sub_at_zero, sub_at_zero, by simp [arch_zero'], ?_⟩
    simp only [vecMulVec_zero', Matrix.mulVec_zero, Matrix.zero_vecMulVec, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, map_zero, Prod.fst_zero, Prod.snd_zero, arch_zero']
    rfl
  · rintro l ⟨a, c, z, ha, hc, hz, hz1, rfl⟩ l' ⟨a', c', z', ha', hc', hz', hz1', rfl⟩
    refine ⟨a + a', c + c', z + z', sub_at_add ha ha', sub_at_add hc hc', sub_at_add hz hz', ?_, ?_⟩
    · rw [map_add, Prod.fst_add, sub_arch_add, hz1, hz1', add_zero]
    · have : Matrix.vecMulVec (incV F H.x) (a + a') + Matrix.vecMulVec (incM F H.ι *ᵥ (c + c')) (incV F H'.x) +
          incM F H.ι * (z + z') * (incM F H'.ι)ᵀ =
          (Matrix.vecMulVec (incV F H.x) a + Matrix.vecMulVec (incM F H.ι *ᵥ c) (incV F H'.x) +
            incM F H.ι * z * (incM F H'.ι)ᵀ) +
          (Matrix.vecMulVec (incV F H.x) a' + Matrix.vecMulVec (incM F H.ι *ᵥ c') (incV F H'.x) +
            incM F H.ι * z' * (incM F H'.ι)ᵀ) := by
        rw [Matrix.vecMulVec_add, Matrix.mulVec_add, Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]; abel
      rw [this]
      ext : 1 <;> simp only [Prod.fst_add, Prod.snd_add, LinearEquiv.map_add, sub_arch_add] <;> abel
  · rintro t l ⟨a, c, z, ha, hc, hz, hz1, rfl⟩
    refine ⟨realAd F t • a, realAd F t • c, realAd F t • z, sub_at_smul _ ha, sub_at_smul _ hc, sub_at_smul _ hz, ?_, ?_⟩
    · rw [map_smul, Prod.smul_fst, sub_arch_smul, hz1, smul_zero]
    · have : Matrix.vecMulVec (incV F H.x) (realAd F t • a) + Matrix.vecMulVec (incM F H.ι *ᵥ (realAd F t • c)) (incV F H'.x) +
          incM F H.ι * (realAd F t • z) * (incM F H'.ι)ᵀ =
          realAd F t • (Matrix.vecMulVec (incV F H.x) a + Matrix.vecMulVec (incM F H.ι *ᵥ c) (incV F H'.x) +
            incM F H.ι * z * (incM F H'.ι)ᵀ) := by
        ext i j
        simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_mul,
          smul_add, mul_smul_comm, smul_mul_assoc]
      rw [this, map_smul, Prod.smul_fst, Prod.smul_snd, sub_arch_smul, sub_arch_smul]
      rfl

end GlobalTheory.ArchSchB
