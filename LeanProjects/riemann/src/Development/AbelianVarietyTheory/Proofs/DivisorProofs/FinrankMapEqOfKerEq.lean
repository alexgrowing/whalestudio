import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

section Gen

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def ksForm (φ : LinearMap.BilinForm k H) (Fil : Submodule k H) :
    (H →ₗ[k] H) →ₗ[k] LinearMap.BilinForm k Fil where
  toFun g := φ.compl₁₂ (g ∘ₗ Fil.subtype) Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

@[simp] theorem ksForm_apply (φ : LinearMap.BilinForm k H) (Fil : Submodule k H) (g : H →ₗ[k] H)
    (x y : Fil) : ksForm φ Fil g x y = φ (g x) y := rfl

def blockSym {E ι : Type*} [AddCommGroup E] [Module k E] (W : ι → Submodule k E) (c : ι → ι) :
    Submodule k (LinearMap.BilinForm k E) where
  carrier := {B | (∀ x y, B x y = B y x) ∧ ∀ i j, j ≠ c i → ∀ x ∈ W i, ∀ y ∈ W j, B x y = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' {B C} hB hC := ⟨fun x y => by simp [hB.1 x y, hC.1 x y],
    fun i j hij x hx y hy => by simp [hB.2 i j hij x hx y hy, hC.2 i j hij x hx y hy]⟩
  smul_mem' a B hB := ⟨fun x y => by simp [hB.1 x y],
    fun i j hij x hx y hy => by simp [hB.2 i j hij x hx y hy]⟩

theorem ksDim_finrank [FiniteDimensional k H] (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H)
    (Fil Z : Submodule k H) : KSDim ρ φ Fil Z (finrank k ((ksSub ρ φ Fil Z).map (cls Fil))) := by
  set M := (ksSub ρ φ Fil Z).map (cls Fil) with hM
  let b := Module.finBasis k M
  have hb : ∀ i, ∃ f ∈ ksSub ρ φ Fil Z, cls Fil f = (b i : Fil →ₗ[k] H ⧸ Fil) := fun i => (b i).2
  choose f hf hfb using hb
  have key : ∀ (g : H →ₗ[k] H) (c : Fin (finrank k M) → k),
      (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
        cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil) := fun g c => by
    simp_rw [← hfb]
    simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  refine ⟨f, hf, fun g hg => ?_⟩
  let m : M := ⟨cls Fil g, g, hg, rfl⟩
  have hsum : ∀ c : Fin (finrank k M) → k, (cls Fil g = ∑ i, c i • (b i : Fil →ₗ[k] H ⧸ Fil)) ↔
      m = ∑ i, c i • b i := fun c => by
    rw [Subtype.ext_iff]; simp [m]
  refine ⟨b.equivFun m, (key g _).2 ((hsum _).2 ?_), fun c hc => ?_⟩
  · rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  · have := (hsum c).1 ((key g c).1 hc)
    rw [this, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem finrank_map_add_ker {M N : Type*} [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [AddCommGroup N] [Module k N] (p : Submodule k M) (f : M →ₗ[k] N) :
    finrank k (p.map f) + finrank k (LinearMap.ker (f ∘ₗ p.subtype)) = finrank k p := by
  rw [← LinearMap.finrank_range_add_finrank_ker (f ∘ₗ p.subtype), LinearMap.range_comp,
    Submodule.range_subtype]

end Gen

end GlobalTheory.UPel.Sm.KSCount
