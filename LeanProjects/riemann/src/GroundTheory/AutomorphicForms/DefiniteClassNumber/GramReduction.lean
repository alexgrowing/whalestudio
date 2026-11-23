import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.Reduction

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix Submodule
open scoped RealInnerProductSpace

variable {J : Type*} [Fintype J]

def GramSpace (_G : Matrix J J ℝ) : Type _ := J → ℝ

instance (G : Matrix J J ℝ) : AddCommGroup (GramSpace G) := inferInstanceAs (AddCommGroup (J → ℝ))

instance (G : Matrix J J ℝ) : Module ℝ (GramSpace G) := inferInstanceAs (Module ℝ (J → ℝ))

instance (G : Matrix J J ℝ) : FiniteDimensional ℝ (GramSpace G) :=
  inferInstanceAs (FiniteDimensional ℝ (J → ℝ))

def toGram (G : Matrix J J ℝ) : (J → ℝ) ≃ₗ[ℝ] GramSpace G := LinearEquiv.refl ℝ (J → ℝ)

@[instance_reducible]
def gramCore (G : Matrix J J ℝ) (hs : Gᵀ = G) (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) :
    InnerProductSpace.Core ℝ (GramSpace G) where
  inner x y := (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
  conj_inner_symm x y := by
    show (toGram G).symm y ⬝ᵥ (G *ᵥ (toGram G).symm x) = (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]
  re_inner_nonneg x := by
    show 0 ≤ (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm x)
    by_cases hx : (toGram G).symm x = 0
    · rw [hx]; simp
    · exact (hpos _ hx).le
  add_left x y z := by
    show (toGram G).symm (x + y) ⬝ᵥ _ = (toGram G).symm x ⬝ᵥ _ + (toGram G).symm y ⬝ᵥ _
    rw [map_add, add_dotProduct]
  smul_left x y r := by
    show (toGram G).symm (r • x) ⬝ᵥ _ = r * ((toGram G).symm x ⬝ᵥ _)
    rw [map_smul, smul_dotProduct, smul_eq_mul]
  definite x hx := by
    by_contra h
    have h' : (toGram G).symm x ≠ 0 := by simpa using h
    have := hpos _ h'
    exact (ne_of_gt this) hx

theorem gram_mul_self_le (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (x y : J → ℝ) :
    (x ⬝ᵥ (G *ᵥ y)) * (x ⬝ᵥ (G *ᵥ y)) ≤ (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) := by
  let core := gramCore G hs hpos
  let _ : NormedAddCommGroup (GramSpace G) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (GramSpace G) := .ofCore _
  exact real_inner_mul_inner_self_le (toGram G x) (toGram G y)

theorem exists_short_basis_gram (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (L : AddSubgroup (J → ℝ)) (μ : ℝ)
    (hμ : 0 < μ) (hL : span ℝ (L : Set (J → ℝ)) = ⊤)
    (hD : span ℝ {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} = ⊤)
    (hmin : ∀ y : J → ℝ, (∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n) → y ≠ 0 →
      μ ^ 2 ≤ y ⬝ᵥ (G *ᵥ y)) :
    ∃ e : Fin (Fintype.card J) → (J → ℝ), LinearIndependent ℝ e ∧
      ∀ i, e i ∈ L ∧ e i ⬝ᵥ (G *ᵥ e i) ≤ shortBasisBound (Fintype.card J) μ ^ 2 := by
  let core := gramCore G hs hpos
  let _ : NormedAddCommGroup (GramSpace G) := core.toNormedAddCommGroup
  let _ : InnerProductSpace ℝ (GramSpace G) := .ofCore _
  have hinner : ∀ x y : J → ℝ, ⟪toGram G x, toGram G y⟫ = x ⬝ᵥ (G *ᵥ y) := fun _ _ => rfl
  have hnorm : ∀ x : J → ℝ, ‖toGram G x‖ ^ 2 = x ⬝ᵥ (G *ᵥ x) := by
    intro x
    rw [← real_inner_self_eq_norm_sq, hinner]
  let L' : AddSubgroup (GramSpace G) := L.map (toGram G).toLinearMap.toAddMonoidHom
  have memL' : ∀ z, z ∈ L' ↔ (toGram G).symm z ∈ L := by
    intro z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨_, hz, by simp⟩
  have hdual : ∀ z, z ∈ latticeDual L' ↔ (toGram G).symm z ∈
      {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} := by
    intro z
    constructor
    · intro hz x hx
      have := hz (toGram G x) ((memL' _).2 (by simpa using hx))
      simpa [← hinner] using this
    · intro hz x hx
      have := hz _ ((memL' x).1 hx)
      rw [← hinner] at this
      simpa using this
  have hLspan : span ℝ (L' : Set (GramSpace G)) = ⊤ := by
    have : (L' : Set (GramSpace G)) = (toGram G) '' (L : Set (J → ℝ)) := by
      ext z
      rw [SetLike.mem_coe, memL', Set.mem_image]
      constructor
      · intro h; exact ⟨_, h, by simp⟩
      · rintro ⟨x, hx, rfl⟩; simpa using hx
    rw [this, ← LinearEquiv.coe_coe, span_image, hL, Submodule.map_top,
      LinearMap.range_eq_top.2 (toGram G).surjective]
  have hDspan : span ℝ (latticeDual L' : Set (GramSpace G)) = ⊤ := by
    have : (latticeDual L' : Set (GramSpace G)) =
        (toGram G) '' {y : J → ℝ | ∀ x ∈ L, ∃ n : ℤ, y ⬝ᵥ (G *ᵥ x) = n} := by
      ext z
      rw [SetLike.mem_coe, hdual, Set.mem_image]
      constructor
      · intro h; exact ⟨_, h, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this, ← LinearEquiv.coe_coe, span_image, hD, Submodule.map_top,
      LinearMap.range_eq_top.2 (toGram G).surjective]
  have hmin' : ∀ z ∈ latticeDual L', z ≠ 0 → μ ≤ ‖z‖ := by
    intro z hz hz0
    have h1 := hmin ((toGram G).symm z) ((hdual z).1 hz) (by simpa using hz0)
    rw [← hnorm, LinearEquiv.apply_symm_apply] at h1
    exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _) |>.trans_eq' rfl
  obtain ⟨e, hli, he⟩ := exists_short_basis (Fintype.card J) (X := GramSpace G)
    (by rw [show finrank ℝ (GramSpace G) = finrank ℝ (J → ℝ) from rfl, finrank_fintype_fun_eq_card])
    L' μ hμ hLspan hDspan hmin'
  refine ⟨fun i => (toGram G).symm (e i), hli.map' (toGram G).symm.toLinearMap (by simp), fun i => ?_⟩
  refine ⟨(memL' _).1 (he i).1, ?_⟩
  rw [← hnorm, LinearEquiv.apply_symm_apply]
  have h0 := norm_nonneg (e i)
  exact pow_le_pow_left₀ h0 (he i).2 2

end GroundTheory.Automorphic
