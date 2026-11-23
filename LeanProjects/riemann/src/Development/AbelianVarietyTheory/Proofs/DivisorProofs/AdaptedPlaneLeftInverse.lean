import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaneLeftInv

theorem exists_leftInv_of_span {E : Type} [Field E] {d d₁ : ℕ} (hd : d = d₁ + 2) (ι : Matrix (Fin d) (Fin d₁) E)
    (x y : Fin d → E) (S : Set (Fin d → E)) (hS : Submodule.span E S = ⊤)
    (h : ∀ z ∈ S, ∃ (s t : E) (u : Fin d₁ → E), z = s • x + ι *ᵥ u + t • y) :
    ∃ L : Matrix (Fin d₁) (Fin d) E, L * ι = 1 := by
  let T : ((Fin d₁ → E) × (E × E)) →ₗ[E] (Fin d → E) :=
    ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ x).coprod (LinearMap.toSpanSingleton E _ y))
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hS, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, rfl⟩ := h z hz
    refine ⟨(u, (s, t)), ?_⟩
    simp only [T, LinearMap.coprod_apply, Matrix.mulVecLin_apply, LinearMap.toSpanSingleton_apply]
    abel
  have hrk : Module.finrank E ((Fin d₁ → E) × (E × E)) = Module.finrank E (Fin d → E) := by
    simp [Module.finrank_prod, hd]
  have hinj : Function.Injective T := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj
  have hker : LinearMap.ker (Matrix.toLin' ι) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h0 : T (u, (0, 0)) = T 0 := by
      rw [map_zero]
      simpa [T] using hu
    exact congrArg Prod.fst (hinj h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_leftInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ r' s' i₀ i₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ L : Matrix (Fin d₁) (Fin d) E, L * H'.ι = 1 := by
  intro F E _ _ _ _ _ σ B d d₁ r' s' i₀ i₁ W W₁ H' hW hH
  refine exists_leftInv_of_span hH.rank H'.ι H'.x H'.y (W.L : Set (Fin d → E)) hW.lat.span_eq_top ?_
  intro z hz
  obtain ⟨s, t, u, -, -, -, hz'⟩ := hH.split z hz
  exact ⟨s, t, u, hz'⟩

end GlobalTheory.PlaneLeftInv
