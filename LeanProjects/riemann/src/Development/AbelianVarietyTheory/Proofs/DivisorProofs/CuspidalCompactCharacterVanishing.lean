import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open MeasureTheory Matrix

namespace GlobalTheory

theorem typeFunction_unip_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (e : ι ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → K) → GL ι K)
    (hu : ∀ X, (u X : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X Y : Fin a → Fin b → K) : u (Y + X) = u X * u Y := by
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.of_add_of]

theorem typeFunction_constantTerm_eq_zero :
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro K _ _ _ _ _ _ ι _ _ J hJo hJc χ hχ hnt f hf1 hf0
  have hR : ∀ g j (hj : j ∈ J), f (g * j) = f g * (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hg hj), hf1 g hg]
      have : (⟨g * j, J.mul_mem hg hj⟩ : J) = ⟨g, hg⟩ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_right hj).1 h)), zero_mul]
  have hL : ∀ g j (hj : j ∈ J), f (j * g) = (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * f g := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hj hg), hf1 g hg]
      have : (⟨j * g, J.mul_mem hj hg⟩ : J) = ⟨j, hj⟩ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_left hj).1 h)), mul_zero]
  have hRk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (g * y) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hR g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, mul_one] at this
    exact this
  have hLk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (y * g) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hL g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, one_mul] at this
    exact this
  have hNo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)),
      hNo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hRk _ hx g
      rwa [mul_inv_cancel_left] at this
  · exact HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => hf0 g hg)
  · intro x hx y hy g
    rw [hRk y hy, hLk x hx]
  · intro a b e ha hb μ hμ u hu g h
    obtain ⟨Y, hY, hne⟩ := hnt a b e ha hb u hu h
    have key : ∀ X, f (g * (h⁻¹ * u (Y + X) * h)) =
        f (g * (h⁻¹ * u X * h)) * (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) := by
      intro X
      rw [← hR _ _ hY, typeFunction_unip_add e u hu]
      congr 1
      group
    have h1 := integral_add_left_eq_self (μ := μ) (fun X => f (g * (h⁻¹ * u X * h))) Y
    simp only [key] at h1
    rw [integral_mul_const] at h1
    have hc : (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro hc
      exact hne (inv_eq_one.1 (Units.val_eq_one.1 hc))
    by_contra hI
    exact hc (mul_left_cancel₀ hI (h1.trans (mul_one _).symm))

end GlobalTheory
