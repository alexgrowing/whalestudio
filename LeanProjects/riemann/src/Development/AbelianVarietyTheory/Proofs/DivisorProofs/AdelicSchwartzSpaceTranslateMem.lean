import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.SchwartzTranslate

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def transl (a : κ → AdeleRing (𝓞 F) F) : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) where
  toFun φ x := φ (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem SB_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] (b : X) {g : X → ℂ}
    (hg : g ∈ SB X) : (fun y => g (y + b)) ∈ SB X :=
  ⟨hg.1.comp_continuous (continuous_add_const b), hg.2.comp_homeomorph (Homeomorph.addRight b)⟩

theorem pureA_translate (a : κ → AdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    transl F a (pureA F f g) = pureA F (f.compSubConstCLM ℂ (-fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1))
      (fun y => g (y + fun i => (a i).2)) := by
  funext x
  simp only [transl, LinearMap.coe_mk, AddHom.coe_mk, pureA, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  congr 2
  funext i
  exact map_add _ _ _

theorem schA_translate (a : κ → AdeleRing (𝓞 F) F) {φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F κ) :
    (fun x => φ (x + a)) ∈ schA F κ := by
  have key : schA F κ ≤ (schA F κ).comap (transl F a) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, g, hg, rfl⟩
    show transl F a (pureA F f g) ∈ schA F κ
    rw [pureA_translate]
    exact Submodule.subset_span ⟨_, _, SB_translate _ hg, rfl⟩
  exact key hφ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : κ → AF F), ∀ φ ∈ schA F κ,
    (fun x => φ (x + a)) ∈ schA F κ :=
  fun F _ _ _ _ a φ hφ => schA_translate F a hφ

end GlobalTheory.SchwartzTranslate

end
