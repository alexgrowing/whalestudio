import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.IsoCoset

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

omit [NumberField E] in

theorem incl_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
  haveI : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AF F ⊗[F] E) := inferInstance
  exact (inclR (F := F) (E := E) (AF F)).injective

omit [NumberField E] in
theorem incV_inj {x y : Fin n → E} (h : incV F x = incV F y) : x = y :=
  funext fun i => incl_inj (F := F) (congrFun h i)

omit [NumberField E] in
theorem mat_mul_vec (g h : UA σ J) (v : Fin n → AE F E) : mat (g * h) *ᵥ v = mat g *ᵥ (mat h *ᵥ v) := by
  rw [Matrix.mulVec_mulVec]; rfl

omit [NumberField E] in
theorem mat_one_vec (v : Fin n → AE F E) : mat (1 : UA σ J) *ᵥ v = v := by
  have : mat (1 : UA σ J) = 1 := rfl
  rw [this, Matrix.one_mulVec]

omit [NumberField E] in
theorem inv_vec {g : UA σ J} {v w : Fin n → AE F E} (h : mat g *ᵥ v = w) : mat g⁻¹ *ᵥ w = v := by
  rw [← h, ← mat_mul_vec, inv_mul_cancel, mat_one_vec]

omit [NumberField E] in

theorem mem_closure_iff (v : Fin n → AE F E) (g : UA σ J) :
    g ∈ Subgroup.closure {g : UA σ J | mat g *ᵥ v = v} ↔ mat g *ᵥ v = v := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact mat_one_vec v
  | mul x y _ _ hx hy => rw [mat_mul_vec, hy, hx]
  | inv x _ hx => exact inv_vec hx

omit [NumberField E] in

theorem rat_act {δ : UA σ J} (hδ : δ ∈ ratU σ J) (x : Fin n → E) :
    ∃ y : Fin n → E, mat δ *ᵥ incV F x = incV F y ∧ form σ J y y = form σ J x x := by
  obtain ⟨A, hA⟩ := Subgroup.mem_subgroupOf.1 hδ
  have hm : mat δ = (A : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    unfold mat; rw [← hA]; rfl
  have hU : (mat δ)ᵀ * incM F J * (mat δ).map (cA σ) = incM F J := δ.2
  have hE : (A : Matrix (Fin n) (Fin n) E)ᵀ * J * (A : Matrix (Fin n) (Fin n) E).map σ = J := by
    apply Matrix.map_injective (incl_inj (F := F) (E := E))
    show _ = incM F J
    rw [← hU, hm]
    show ((A : Matrix (Fin n) (Fin n) E)ᵀ * J * (A : Matrix (Fin n) (Fin n) E).map σ).map (inclR (F := F) (AF F)) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
  refine ⟨(A : Matrix (Fin n) (Fin n) E) *ᵥ x, ?_, ?_⟩
  · funext i
    rw [hm]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) (A : Matrix (Fin n) (Fin n) E) x i).symm
  · have h1 : (fun i => σ (((A : Matrix (Fin n) (Fin n) E) *ᵥ x) i)) =
        (A : Matrix (Fin n) (Fin n) E).map σ *ᵥ fun i => σ (x i) :=
      funext fun i => RingHom.map_mulVec (σ : E →+* E) (A : Matrix (Fin n) (Fin n) E) x i
    unfold form
    rw [h1]
    conv_rhs => rw [← hE]
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
      Matrix.vecMul_transpose]

theorem coset : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x₀ : Fin n → E), form σ J x₀ x₀ = 0 → x₀ ≠ 0 →
    ∀ γ : {x : Fin n → E // x ≠ 0 ∧ form σ J x x = 0} → UA σ J, (∀ x, γ x ∈ ratU σ J ∧ mat (γ x) *ᵥ incV F x.1 = incV F x₀) →
    ∀ δ ∈ ratU σ J, ∃! x, δ * (γ x)⁻¹ ∈ ratU σ J ⊓ Subgroup.closure {g : UA σ J | mat g *ᵥ incV F x₀ = incV F x₀} := by
  intro F E _ _ _ _ _ σ n J x₀ h0 hne γ hγ δ hδ
  obtain ⟨y, hy, hf⟩ := rat_act ((ratU σ J).inv_mem hδ) x₀
  have hy' : mat δ *ᵥ incV F y = incV F x₀ := by simpa using inv_vec hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hne
    apply incV_inj (F := F)
    have hz : incV F (0 : Fin n → E) = 0 := funext fun i => map_zero (inclR (F := F) (E := E) (AF F))
    rw [← hy', hz, Matrix.mulVec_zero]
  refine ⟨⟨y, hy0, hf.trans h0⟩, ⟨(ratU σ J).mul_mem hδ ((ratU σ J).inv_mem (hγ _).1), ?_⟩, ?_⟩
  · refine (mem_closure_iff _ _).2 ?_
    rw [mat_mul_vec, inv_vec (hγ _).2, hy']
  · rintro x ⟨-, hx⟩
    have hx' := (mem_closure_iff _ _).1 hx
    rw [mat_mul_vec, inv_vec (hγ _).2] at hx'
    apply Subtype.ext
    apply incV_inj (F := F)
    rw [← inv_vec hx', hy]

end GlobalTheory.ThK.IsoCoset
