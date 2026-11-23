import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.FormSection

theorem exists_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    ∀ x : Fin n → E, (∃ z ∈ L, form σ J z x ≠ 0) →
    ∃ y₀ : Fin n → E, form σ J y₀ x = 1 ∧ ∀ z ∈ L, form σ J z x • y₀ ∈ L := by
  intro F E _ _ _ _ _ σ n J L hL x ⟨z₀, hz₀L, hz₀⟩
  classical

  let φ : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => form σ J z x
      map_add' := fun a b => by simp [form, add_dotProduct]
      map_smul' := fun a z => by
        simp only [form, RingHom.id_apply]
        rw [← algebraMap_smul E a z, smul_dotProduct, smul_eq_mul, Algebra.smul_def] }
  have hφ : ∀ z, φ z = form σ J z x := fun _ => rfl
  have hφE : ∀ (c : E) z, form σ J (c • z) x = c * form σ J z x := by
    intro c z; simp [form, smul_dotProduct]
  let I : Submodule (𝓞 E) E := L.map φ
  have hIfg : I.FG := hL.map φ
  let I' : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨I, FractionalIdeal.isFractional_of_fg hIfg⟩
  have hmemI : ∀ z ∈ L, form σ J z x ∈ I' := fun z hz => ⟨z, hz, rfl⟩
  have hI0 : I' ≠ 0 := by
    intro h
    have := hmemI z₀ hz₀L
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact hz₀ this
  have hone : I' * I'⁻¹ = 1 := mul_inv_cancel₀ hI0
  let S : Submodule (𝓞 E) E :=
    { carrier := {e | ∃ y₀ : Fin n → E, form σ J y₀ x = e ∧ ∀ c ∈ I, c • y₀ ∈ L}
      add_mem' := by
        rintro _ _ ⟨y₁, rfl, h₁⟩ ⟨y₂, rfl, h₂⟩
        refine ⟨y₁ + y₂, by simp [form, add_dotProduct], fun c hc => ?_⟩
        rw [smul_add]; exact L.add_mem (h₁ c hc) (h₂ c hc)
      zero_mem' := ⟨0, by simp [form], fun c _ => by simp⟩
      smul_mem' := by
        rintro a _ ⟨y, rfl, h⟩
        refine ⟨a • y, ?_, fun c hc => ?_⟩
        · rw [← hφ, ← hφ, map_smul]
        · rw [smul_comm]; exact L.smul_mem a (h c hc) }
  have hle : I * ((I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) ≤ S := by
    refine Submodule.mul_le.mpr fun i hi j hj => ?_
    obtain ⟨z, hz, rfl⟩ := hi
    refine ⟨j • z, ?_, fun c hc => ?_⟩
    · rw [hφE, hφ, mul_comm]
    · have hcj : j * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
        (FractionalIdeal.mem_inv_iff hI0).mp hj c hc
      obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcj
      rw [smul_smul, mul_comm, ← ha, algebraMap_smul]
      exact L.smul_mem a hz
  have h1 : (1 : E) ∈ S := by
    apply hle
    have : (1 : E) ∈ ((I' * I'⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [hone]; exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
    rwa [FractionalIdeal.coe_mul] at this
  obtain ⟨y₀, hy₀, hL'⟩ := h1
  exact ⟨y₀, hy₀, fun z hz => hL' _ (hmemI z hz)⟩

end GlobalTheory.FormSection
