import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTowerPropertiesStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

theorem dot_ne_zero_of_hasSig_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M n 0)
    (x : Fin n → ℂ) (hx : x ≠ 0) : x ⬝ᵥ M *ᵥ star x ≠ 0 := by
  obtain ⟨-, A, hA⟩ := h
  have hm1 : (-1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 := Subsingleton.elim _ _
  rw [hm1, Matrix.fromBlocks_one] at hA
  have h1 : Aᵀ * (M * A.map star) = 1 := by rw [← Matrix.mul_assoc]; exact hA
  have h2 : (M * A.map star) * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.sumEmpty (Fin n) (Fin 0))).1 h1
  set y := (M * A.map star)ᵀ *ᵥ x with hy
  have hxy : A *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, ← Matrix.transpose_transpose A, ← Matrix.transpose_mul,
      Matrix.transpose_transpose, h2, Matrix.transpose_one, Matrix.one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h0; apply hx; rw [← hxy, h0, Matrix.mulVec_zero]
  have hsx : star x = A.map star *ᵥ star y := by
    rw [← hxy]; ext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : x ⬝ᵥ M *ᵥ star x = y ⬝ᵥ star y := by
    rw [hsx, Matrix.mulVec_mulVec, ← hxy, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [key]
  intro h0
  apply hy0
  exact dotProduct_self_star_eq_zero.1 h0

theorem map_form_self {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (z : Fin n → E) :
    τ (form σ J z z) = (fun i => τ (z i)) ⬝ᵥ J.map τ *ᵥ star (fun i => τ (z i)) := by
  simp [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hτ]

theorem exists_adapted_plane_of_isotropic : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G₁ : Geo σ a b) X om₁ om₁', IsTriple B G₁ X om₁ om₁' →
    (∃ z : Fin (a + b) → E, z ≠ 0 ∧ form σ G₁.W.J z z = 0) →
    ∃ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' ∧
      ∃ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ := by
  intro hK F E _ _ _ _ _ σ B a b G₁ X om₁ om₁' hT hz
  obtain ⟨hTA, hTB⟩ := GlobalTheory.T.theta_tower_properties hK.base
  have hg := hT.geo
  have hlt := hg.lt
  have hab := hg.aBig
  by_cases hq : 1 ≤ G₁.q
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    obtain ⟨V, V', W, hT', G₂, H, H', hC, -⟩ := hTB F E σ B a b' G₁ X om₁ om₁' hT hq
    exact ⟨V, V', W, hT', a + b', G₂.W, H', a, a + b' + 1, hC.hH'⟩
  · have hq0 : G₁.q = 0 := by omega
    have hp : 1 ≤ G₁.p := by
      by_contra hp0
      have hp0 : G₁.p = 0 := by omega
      obtain ⟨z, hz0, hzz⟩ := hz
      obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
      let w : NumberField.InfinitePlace F := NumberField.InfinitePlace.mk φ
      have hs := hg.hW.sig w
      rw [hp0, hq0] at hs
      simp only [add_zero, Nat.sub_zero] at hs
      let τ : E →+* ℂ := (B.emb w).1
      have hτ : ∀ x, τ (σ x) = star (τ x) := fun x => hT.base.cm.2.2.2 τ x
      have hx : (fun i => τ (z i)) ≠ 0 := by
        intro h0; apply hz0; funext i
        have := congrFun h0 i
        simpa using this
      apply dot_ne_zero_of_hasSig_pos _ hs _ hx
      have hsm : ∀ (c : ℂ) (M : Matrix (Fin (a + b)) (Fin (a + b)) ℂ) (v : Fin (a + b) → ℂ), (c • M) *ᵥ v = c • (M *ᵥ v) := by
        intro c M v; ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [hsm, dotProduct_smul, ← map_form_self σ τ hτ, hzz, map_zero, smul_zero]
    obtain ⟨a₀, rfl⟩ : ∃ a₀, a = a₀ + 2 := ⟨a - 2, by omega⟩
    obtain ⟨V, V', W, hT', G₂, H, H', hC, -⟩ := hTA F E σ B a₀ b G₁ X om₁ om₁' hT hq0 hp
    exact ⟨V, V', W, hT', a₀ + b, G₂.W, H', 0, a₀ + 1, hC.hH'⟩

end GlobalTheory.ConeSmallMidJB
