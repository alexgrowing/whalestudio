import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem incM_mulVec_incV {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (z : Fin n → E) :
    incM F A *ᵥ incV F z = incV F (A *ᵥ z) := by
  funext i
  simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem single_eq_incV {n : ℕ} (j : Fin n) :
    (Pi.single j (1 : AE F E) : Fin n → AE F E) = incV F (Pi.single j (1 : E)) := by
  funext i
  by_cases h : i = j
  · subst h; simp [incV]
  · simp [incV, Pi.single_apply, h]

theorem fA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    fA σ J (incV F v) (incV F w) = inclR (F := F) (AF F) (form σ J v w) := by
  simp [fA, incV, form, incM, cA_inclR, dotProduct, Matrix.mulVec, map_sum, map_mul]

theorem fA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    fA σ J (v + v') w = fA σ J v w + fA σ J v' w := by
  simp [fA, add_dotProduct]

theorem fA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : AE F E) (v w : Fin n → AE F E) :
    fA σ J (c • v) w = c * fA σ J v w := by
  simp [fA, smul_dotProduct]

variable {σ : E →ₐ[F] E}

theorem mat_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u v : UA σ J) : mat (u * v) = mat u * mat v := rfl

theorem mat_one' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul' {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u : UA σ J) : mat u⁻¹ * mat u = 1 := by
  show ((u.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * u.1.1 = 1
  exact Units.inv_mul u.1

theorem unip_spec {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {u : UA σ W.J} (hu : u ∈ unip σ W H') :
    mat u *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨by simp [mat_one'], fun z => ⟨0, by simp [mat_one']⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨by rw [mat_mul', ← Matrix.mulVec_mulVec, hy.1, hx.1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 z
    obtain ⟨b, hb⟩ := hy.2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul', ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, ha, add_smul, add_assoc]
  | inv x _ hx =>
    have h1 : ∀ w, mat x⁻¹ *ᵥ (mat x *ᵥ w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    have hx1 : mat x⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      have := h1 (incV F H'.x); rwa [hx.1] at this
    refine ⟨hx1, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hx.2 z
    refine ⟨-a, ?_⟩
    have h2 := h1 (incM F H'.ι *ᵥ z)
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx1] at h2
    rw [neg_smul]
    exact eq_add_neg_of_add_eq h2

end GlobalTheory.ThK.UnipDom.Additive

open GlobalTheory.ThK.UnipDom.Additive in
theorem GlobalTheory.ThK.UnipDom.coA_mul_of_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ u ∈ unip σ W H', ∀ v ∈ unip σ W H', coA σ W.J H' (u * v) = coA σ W.J H' u + coA σ W.J H' v := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ _ _ hA u hu v hv
  funext j
  set e : Fin d → AE F E := incM F H'.ι *ᵥ Pi.single j 1 with he
  have hval : ∀ c : AE F E, fA σ W.J (e + c • incV F H'.x) (incV F H'.y) = c := by
    intro c
    rw [fA_add_left, fA_smul_left, fA_incV, hA.xy, map_one, mul_one, he, single_eq_incV,
      incM_mulVec_incV, fA_incV, (hA.orth _).2, map_zero, zero_add]
  obtain ⟨a, ha⟩ := (unip_spec hu).2 (Pi.single j 1)
  obtain ⟨b, hb⟩ := (unip_spec hv).2 (Pi.single j 1)
  have hux := (unip_spec hu).1
  have huv : mat (u * v) *ᵥ e = e + (a + b) • incV F H'.x := by
    rw [mat_mul', ← Matrix.mulVec_mulVec, he, hb, Matrix.mulVec_add, Matrix.mulVec_smul, hux, ha, add_smul, add_assoc]
  simp only [Pi.add_apply, coA]
  rw [← he, huv, hval, ha, ← he, hval, hb, ← he, hval]
