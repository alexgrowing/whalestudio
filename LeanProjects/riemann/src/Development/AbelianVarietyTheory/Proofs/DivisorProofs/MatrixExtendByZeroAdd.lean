import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.AdaptEv

def ext0 {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → R) : κ → R :=
  fun k => Sum.elim (fun _ => 0) a (eq k)

def prodVac {κ ι κ₁ R : Type} (eq : κ ≃ ι ⊕ κ₁) (A : (ι → R) → ℂ) (φ : (κ₁ → R) → ℂ) : (κ → R) → ℂ :=
  fun x => A (fun i => x (eq.symm (Sum.inl i))) * φ (fun j => x (eq.symm (Sum.inr j)))

def restrL {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) : ((κ → R) → ℂ) →ₗ[ℂ] (κ₁ → R) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ext0 eq)

theorem restrL_apply {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (Φ : (κ → R) → ℂ) (y : κ₁ → R) :
    restrL eq Φ y = Φ (ext0 eq y) := rfl

theorem ext0_inl {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → R) (i : ι) :
    ext0 eq a (eq.symm (Sum.inl i)) = 0 := by simp [ext0]

theorem ext0_inr {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → R) (j : κ₁) :
    ext0 eq a (eq.symm (Sum.inr j)) = a j := by simp [ext0]

theorem prodVac_ext0 {κ ι κ₁ R : Type} [Zero R] (eq : κ ≃ ι ⊕ κ₁) (A : (ι → R) → ℂ) (φ : (κ₁ → R) → ℂ)
    (y : κ₁ → R) : prodVac eq A φ (ext0 eq y) = A 0 * φ y := by
  simp only [prodVac, ext0_inl, ext0_inr]; rfl

theorem dotProduct_ext0 {κ ι κ₁ R : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] [CommRing R]
    (eq : κ ≃ ι ⊕ κ₁) (a b : κ₁ → R) : ext0 eq a ⬝ᵥ ext0 eq b = a ⬝ᵥ b := by
  simp only [dotProduct]
  rw [← eq.symm.sum_comp, Fintype.sum_sum_type]
  simp [ext0]

theorem matrixExtendByZero_add {κ ι κ₁ R : Type} [AddZeroClass R] (eq : κ ≃ ι ⊕ κ₁) (a b : κ₁ → R) :
    ext0 eq (a + b) = ext0 eq a + ext0 eq b := by
  funext k; simp only [ext0, Pi.add_apply]; cases eq k <;> simp

theorem ext0_dotProduct_of {κ ι κ₁ R : Type} [Fintype κ] [Fintype ι] [Fintype κ₁] [CommRing R]
    (eq : κ ≃ ι ⊕ κ₁) (a : κ₁ → R) (b : κ → R) (hb : ∀ j, b (eq.symm (Sum.inr j)) = 0) : ext0 eq a ⬝ᵥ b = 0 := by
  simp only [dotProduct]
  rw [← eq.symm.sum_comp, Fintype.sum_sum_type]
  simp [ext0, hb]

end GlobalTheory.ThK.AdaptEv

namespace GlobalTheory.ThK.AdaptEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def isoAd {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
  {u | ∃ y, u = Matrix.vecMulVec y (incV F H'.y)} ∪ {u | ∃ z, u = Matrix.vecMulVec (incV F H.y) (incM F H'.ι *ᵥ z)}

end GlobalTheory.ThK.AdaptEv

namespace GlobalTheory.ThK.AdaptEv
theorem prodVac_indicator {κ ι κ₁ R : Type} (eq : κ ≃ ι ⊕ κ₁) (S : Set R) :
    prodVac eq (Set.indicator {x : ι → R | ∀ i, x i ∈ S} 1) (Set.indicator {x : κ₁ → R | ∀ i, x i ∈ S} 1) =
      Set.indicator {x : κ → R | ∀ k, x k ∈ S} 1 := by
  funext x
  have key : (∀ k, x k ∈ S) ↔ (∀ i, x (eq.symm (Sum.inl i)) ∈ S) ∧ ∀ j, x (eq.symm (Sum.inr j)) ∈ S := by
    refine ⟨fun h => ⟨fun i => h _, fun j => h _⟩, fun ⟨ha, hb⟩ k => ?_⟩
    rcases h : eq k with i | j
    · simpa [← h] using ha i
    · simpa [← h] using hb j
  simp only [prodVac]
  by_cases ha : ∀ i, x (eq.symm (Sum.inl i)) ∈ S
  · by_cases hb : ∀ j, x (eq.symm (Sum.inr j)) ∈ S
    · rw [Set.indicator_of_mem (s := {x : ι → R | ∀ i, x i ∈ S}) ha, Set.indicator_of_mem (s := {x : κ₁ → R | ∀ i, x i ∈ S}) hb,
        Set.indicator_of_mem (s := {x : κ → R | ∀ k, x k ∈ S}) (key.2 ⟨ha, hb⟩)]
      simp
    · rw [Set.indicator_of_notMem (s := {x : κ₁ → R | ∀ i, x i ∈ S}) hb,
        Set.indicator_of_notMem (s := {x : κ → R | ∀ k, x k ∈ S}) fun h => hb (key.1 h).2]
      simp
  · rw [Set.indicator_of_notMem (s := {x : ι → R | ∀ i, x i ∈ S}) ha,
      Set.indicator_of_notMem (s := {x : κ → R | ∀ k, x k ∈ S}) fun h => ha (key.1 h).1]
    simp
end GlobalTheory.ThK.AdaptEv
