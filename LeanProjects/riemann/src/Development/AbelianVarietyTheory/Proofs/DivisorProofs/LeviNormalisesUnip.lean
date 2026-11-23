import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviNormal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem conj_mem_gen {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} (H : Plane E n n₁) (g : UA σ J) (c d : AE F E)
    (hcd : c * d = 1) (hx : mat g *ᵥ incV F H.x = c • incV F H.x) (hx' : mat g⁻¹ *ᵥ incV F H.x = d • incV F H.x)
    (hι' : mat g⁻¹ * incM F H.ι = incM F H.ι) (u : UA σ J)
    (hu : mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) :
    mat (g * u * g⁻¹) *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat (g * u * g⁻¹) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x := by
  have hgi : mat g * mat g⁻¹ = 1 := by rw [← mat_mul', mul_inv_cancel, mat_one']
  have hι : mat g * incM F H.ι = incM F H.ι := by
    conv_lhs => rw [← hι']
    rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
  constructor
  · rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, hx', Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hu.1,
      hx, smul_smul, mul_comm, hcd, one_smul]
  · intro z
    obtain ⟨a, ha⟩ := hu.2 z
    refine ⟨a * c, ?_⟩
    have e1 : mat g⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z := by rw [Matrix.mulVec_mulVec, hι']
    rw [mat_mul', mat_mul', ← Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, ha,
      Matrix.mulVec_add, Matrix.mulVec_mulVec, hι, Matrix.mulVec_smul, hx, smul_smul]

theorem conj_mem_closure {G : Type} [Group G] (S : Set G) (g : G) (hS : ∀ u ∈ S, g * u * g⁻¹ ∈ S) :
    ∀ u ∈ Subgroup.closure S, g * u * g⁻¹ ∈ Subgroup.closure S := by
  intro u hu
  have hle : (Subgroup.closure S).map (MulAut.conj g).toMonoidHom ≤ Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨v, hv, rfl⟩
    simpa using hS v hv
  simpa using hle ⟨u, hu, rfl⟩

theorem levi_normalises_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (t : (AE F E)ˣ) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H t 1 m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H ∧ m⁻¹ * u * m ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H t m hL u hu
  obtain ⟨h1, -, h3⟩ := hL
  rw [mat_one', Matrix.mul_one] at h3
  have hmi : mat m⁻¹ * mat m = 1 := by rw [← mat_mul', inv_mul_cancel, mat_one']
  have hι' : mat m⁻¹ * incM F H.ι = incM F H.ι := by
    conv_lhs => rw [← h3]
    rw [← Matrix.mul_assoc, hmi, Matrix.one_mul]
  have hx' : mat m⁻¹ *ᵥ incV F H.x = (t⁻¹).1 • incV F H.x := by
    have e : incV F H.x = t.1 • (mat m⁻¹ *ᵥ incV F H.x) := by
      rw [← Matrix.mulVec_smul, ← h1, Matrix.mulVec_mulVec, hmi, Matrix.one_mulVec]
    conv_rhs => rw [e, smul_smul, Units.inv_mul, one_smul]
  constructor
  · refine conj_mem_closure _ m (fun v hv => conj_mem_gen H m t.1 (t⁻¹).1 (Units.mul_inv t) h1 hx' hι' v hv) u hu
  · have key := conj_mem_closure _ m⁻¹ (fun v hv => by
      have := conj_mem_gen H m⁻¹ (t⁻¹).1 t.1 (Units.inv_mul t) hx' (by rw [inv_inv]; exact h1) (by rw [inv_inv]; exact h3) v hv
      exact this) u hu
    rw [inv_inv] at key
    exact key

end GlobalTheory.LeviNormal
