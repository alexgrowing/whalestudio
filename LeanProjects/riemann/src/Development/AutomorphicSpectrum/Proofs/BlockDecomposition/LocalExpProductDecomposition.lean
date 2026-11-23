import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
open Matrix Topology Filter

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem exists_proj_sup {E : Type*} [AddCommGroup E] [Module ℝ E] (𝔨 𝔟 : Submodule ℝ E) :
    ∃ p q : E →ₗ[ℝ] E, (∀ Z, p Z ∈ 𝔨) ∧ (∀ Z, q Z ∈ 𝔟) ∧
      ∀ Z, Z - p Z - q Z ∈ 𝔨 ⊔ 𝔟 → Z - p Z - q Z = 0 := by
  let f : (𝔨 × 𝔟) →ₗ[ℝ] E := 𝔨.subtype.coprod 𝔟.subtype
  have hr : LinearMap.range f = 𝔨 ⊔ 𝔟 := by
    simp [f, LinearMap.range_coprod]
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict f)
  obtain ⟨P, hP⟩ := (LinearMap.range f).subtype.exists_leftInverse_of_injective (by simp)
  have hsum : ∀ Z, ((s (P Z)).1 : E) + ((s (P Z)).2 : E) = (P Z : E) := by
    intro Z
    have h2 := LinearMap.congr_fun hs (P Z)
    have h3 := congrArg Subtype.val h2
    simpa [f] using h3
  refine ⟨𝔨.subtype ∘ₗ LinearMap.fst ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P, 𝔟.subtype ∘ₗ LinearMap.snd ℝ 𝔨 𝔟 ∘ₗ s ∘ₗ P,
    fun Z => (s (P Z)).1.2, fun Z => (s (P Z)).2.2, fun Z hZ => ?_⟩
  have hid : ∀ W (hW : W ∈ LinearMap.range f), P W = ⟨W, hW⟩ := fun W hW =>
    LinearMap.congr_fun hP ⟨W, hW⟩
  have hval : Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = Z - (P Z : E) := by
    rw [sub_sub, hsum]
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) = 0
  change Z - ((s (P Z)).1 : E) - ((s (P Z)).2 : E) ∈ 𝔨 ⊔ 𝔟 at hZ
  rw [hval] at hZ ⊢
  rw [← hr] at hZ
  have h1 := hid _ hZ
  have h2 : P (Z - (P Z : E)) = P Z - P (P Z : E) := map_sub _ _ _
  have h3 : P (P Z : E) = P Z := hid _ (P Z).2
  rw [h3, sub_self] at h2
  have h4 := congrArg Subtype.val (h1.symm.trans h2)
  simpa using h4

theorem eventually_exp_mul_exp {G : Set A} (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {𝔤 𝔨 𝔟 : Submodule ℝ A} (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {V : Set A} (hV : V ∈ 𝓝 (0 : A)) (hVG : ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨p₀, q₀, hpk, hqb, hr0⟩ := exists_proj_sup 𝔨 𝔟
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap p₀
  let q : A →L[ℝ] A := LinearMap.toContinuousLinearMap q₀
  let r : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p - q
  have hr : ∀ Z, r Z = Z - p Z - q Z := fun Z => rfl
  let Φ : A → A := fun Z =>
    NormedSpace.exp (p Z) * NormedSpace.exp (q Z) * NormedSpace.exp (r Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEl : ∀ l : A →L[ℝ] A, HasStrictFDerivAt (fun Z => NormedSpace.exp (l Z)) l (0 : A) := by
    intro l
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (l 0) := by
      simpa using hE
    exact (h2.comp (0 : A) l.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := ((hEl p).mul' (hEl q)).mul' (hEl r)
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hr]
    abel
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : r ⁻¹' V ∈ 𝓝 (0 : A) := by
    refine r.continuous.continuousAt.preimage_mem_nhds ?_
    simpa using hV
  have himg : Φ '' (r ⁻¹' V) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  have hneg : ∀ X ∈ 𝔤, NormedSpace.exp (-X) ∈ G := by
    intro X hX
    simpa using (h𝔤 X).1 hX (-1)
  have hcancel : ∀ X : A, NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    intro X
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  filter_upwards [himg]
  rintro g ⟨Z, hZ, rfl⟩ hgG
  have hpg : p Z ∈ 𝔤 := hk (hpk Z)
  have hqg : q Z ∈ 𝔤 := hb (hqb Z)
  have hrG : NormedSpace.exp (r Z) ∈ G := by
    have h2 := hmul _ (hneg _ hqg) _ (hmul _ (hneg _ hpg) _ hgG)
    have h3 : NormedSpace.exp (-(q Z)) * (NormedSpace.exp (-(p Z)) * Φ Z) = NormedSpace.exp (r Z) := by
      simp only [Φ]
      rw [← mul_assoc (NormedSpace.exp (-(p Z))), ← mul_assoc (NormedSpace.exp (-(p Z))), hcancel,
        one_mul, ← mul_assoc, hcancel, one_mul]
    rwa [h3] at h2
  have hr𝔤 : r Z ∈ 𝔨 ⊔ 𝔟 := hg (hVG _ hZ hrG)
  have hrz : r Z = 0 := hr0 Z hr𝔤
  refine ⟨p Z, hpk Z, q Z, hqb Z, ?_⟩
  simp [Φ, hrz]

end Banach

theorem eventually_exp_mul_exp_of_isLinRed {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hG : GlobalTheory.LinRed.IsLinRed G) (𝔤 𝔨 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (h𝔤 : ∀ X, X ∈ 𝔤 ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (hV : ∃ V ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ∀ X ∈ V, NormedSpace.exp X ∈ G → X ∈ 𝔤)
    (hk : 𝔨 ≤ 𝔤) (hb : 𝔟 ≤ 𝔤) (hg : 𝔤 ≤ 𝔨 ⊔ 𝔟) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), g ∈ G →
      ∃ X ∈ 𝔨, ∃ Y ∈ 𝔟, g = NormedSpace.exp X * NormedSpace.exp Y := by
  obtain ⟨V, hV, hVG⟩ := hV
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedRing
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedSpace
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.instL2OpNormedAlgebra
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { (inferInstance : Algebra ℝ (Matrix (Fin n) (Fin n) ℂ)) with
      norm_smul_le := fun t X => by
        have : t • X = (t : ℂ) • X := by ext a b; simp
        rw [this, norm_smul]
        simp }
  exact eventually_exp_mul_exp hG.mul_mem h𝔤 hV hVG hk hb hg

end GlobalTheory.CompanionTheory.ClosedSubgroup
