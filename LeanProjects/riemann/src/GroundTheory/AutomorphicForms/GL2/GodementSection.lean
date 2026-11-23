import Mathlib
import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
import GroundTheory.GlobalFields.TateThesis.GlobalZeta

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.Reduction IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def modPow (x : IdeleGroup K) (s : ℂ) : ℂ := ((ideleModule K x : ℝ) : ℂ) ^ s

theorem modPow_mul (x y : IdeleGroup K) (s : ℂ) : modPow (x * y) s = modPow x s * modPow y s := by
  simp only [modPow, map_mul, Positive.val_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (ideleModule K x).2.le (ideleModule K y).2.le s

theorem modPow_add (x : IdeleGroup K) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (ideleModule K x).2.ne')

theorem modPow_one (s : ℂ) : modPow (1 : IdeleGroup K) s = 1 := by
  simp [modPow]

theorem modPow_ne_zero (x : IdeleGroup K) (s : ℂ) : modPow x s ≠ 0 := by
  simp [modPow, (ideleModule K x).2.ne']

def borelElt (a d : IdeleGroup K) (x : 𝔸[K]) : GL (Fin 2) 𝔸[K] where
  val := !![(a : 𝔸[K]), x; 0, (d : 𝔸[K])]
  inv := !![((a⁻¹ : IdeleGroup K) : 𝔸[K]), -(x * ((a⁻¹ : IdeleGroup K) : 𝔸[K]) *
    ((d⁻¹ : IdeleGroup K) : 𝔸[K])); 0, ((d⁻¹ : IdeleGroup K) : 𝔸[K])]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first | ring1 | linear_combination (-(x * ((d⁻¹ : IdeleGroup K) : 𝔸[K]))) * Units.mul_inv a
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

theorem borelElt_val (a d : IdeleGroup K) (x : 𝔸[K]) :
    (borelElt a d x : Matrix (Fin 2) (Fin 2) 𝔸[K]) = !![(a : 𝔸[K]), x; 0, (d : 𝔸[K])] := rfl

theorem det_borelElt (a d : IdeleGroup K) (x : 𝔸[K]) :
    Matrix.GeneralLinearGroup.det (borelElt a d x) = a * d := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, borelElt_val, Matrix.det_fin_two]

theorem vecMul_borelElt (a d : IdeleGroup K) (x : 𝔸[K]) (t : 𝔸[K]) :
    ![0, t] ᵥ* (borelElt a d x : Matrix (Fin 2) (Fin 2) 𝔸[K]) = ![0, t * d] := by
  ext i
  fin_cases i <;> simp [borelElt_val, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

abbrev detI (g : GL (Fin 2) 𝔸[K]) : IdeleGroup K := Matrix.GeneralLinearGroup.det g

def principalSeries (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) : Submodule ℂ (GL (Fin 2) 𝔸[K] → ℂ) where
  carrier := {f | ∀ (a d : IdeleGroup K) (x : 𝔸[K]) (g : GL (Fin 2) 𝔸[K]),
    f (borelElt a d x * g) =
      (χ₁.toIdele a : ℂ) * (χ₂.toIdele d : ℂ) * modPow a s * modPow d (-s) * f g}
  add_mem' {f₁ f₂} h₁ h₂ a d x g := by
    simp only [Pi.add_apply, h₁ a d x g, h₂ a d x g]; ring
  zero_mem' a d x g := by simp
  smul_mem' c f h a d x g := by
    simp only [Pi.smul_apply, smul_eq_mul, h a d x g]; ring

def rightReg (h : GL (Fin 2) 𝔸[K]) (f : GL (Fin 2) 𝔸[K] → ℂ) : GL (Fin 2) 𝔸[K] → ℂ :=
  fun g ↦ f (g * h)

def IsKFinite (f : GL (Fin 2) 𝔸[K] → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)),
    F = rightReg k f})

theorem rightReg_add (h : GL (Fin 2) 𝔸[K]) (f₁ f₂ : GL (Fin 2) 𝔸[K] → ℂ) :
    rightReg h (f₁ + f₂) = rightReg h f₁ + rightReg h f₂ := rfl

theorem rightReg_smul (h : GL (Fin 2) 𝔸[K]) (c : ℂ) (f : GL (Fin 2) 𝔸[K] → ℂ) :
    rightReg h (c • f) = c • rightReg h f := rfl

def principalSeriesKFinite (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) :
    Submodule ℂ (GL (Fin 2) 𝔸[K] → ℂ) where
  carrier := {f | f ∈ principalSeries χ₁ χ₂ s ∧ IsKFinite f}
  add_mem' {f₁ f₂} h₁ h₂ := by
    refine ⟨add_mem h₁.1 h₂.1, ?_⟩
    have : FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)), F = rightReg k f₁}) := h₁.2
    have : FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)), F = rightReg k f₂}) := h₂.2
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      _ ≤ Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)),
        F = rightReg k f₁} ⊔ Submodule.span ℂ {F | ∃ k ∈ (maxCompact :
          Subgroup (AdelicGLn.AdelicGL K 2)), F = rightReg k f₂})
    rintro F ⟨k, hk, rfl⟩
    rw [rightReg_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, hk, rfl⟩)
      (Submodule.subset_span ⟨k, hk, rfl⟩)
  zero_mem' := by
    refine ⟨zero_mem _, ?_⟩
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ : _ ≤ (⊥ : Submodule ℂ _))
    rintro F ⟨k, -, rfl⟩
    exact (Submodule.mem_bot ℂ).2 rfl
  smul_mem' c f h := by
    refine ⟨Submodule.smul_mem _ c h.1, ?_⟩
    have : FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)), F = rightReg k f}) := h.2
    refine Submodule.finiteDimensional_of_le (Submodule.span_le.2 ?_ :
      _ ≤ Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)),
        F = rightReg k f})
    rintro F ⟨k, hk, rfl⟩
    rw [rightReg_smul]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, rfl⟩)

def IsKFiniteVec (Φ : (Fin 2 → 𝔸[K]) → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {F | ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K 2)),
    F = rightTranslate k Φ})

theorem globalZeta_mul_right (F : 𝔸[K] → ℂ) (μ : HeckeCharacter K) (s : ℂ) (d : IdeleGroup K) :
    globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * globalZeta F μ s := by
  set G : IdeleGroup K → ℂ := fun x ↦ F x * (μ.toIdele x : ℂ) * modPow x s with hG
  have hpt : ∀ x : IdeleGroup K, F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s =
      (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) := by
    intro x
    have h1 : modPow d (-s) * modPow d s = 1 := by
      rw [← modPow_add, neg_add_cancel]; simp [modPow]
    have h2 : (((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    simp only [hG, Units.val_mul, map_mul, Circle.coe_mul, modPow_mul]
    linear_combination (-(F ((x : 𝔸[K]) * d) * (μ.toIdele x : ℂ) * modPow x s)) *
      ((((μ.toIdele d)⁻¹ : Circle) : ℂ) * (μ.toIdele d : ℂ) * h1 + h2)
  have : globalZeta (fun t ↦ F (t * (d : 𝔸[K]))) μ s =
      ∫ x, (((μ.toIdele d)⁻¹ : Circle) : ℂ) * modPow d (-s) * G (x * d) ∂ideleMeasure K := by
    simp only [globalZeta]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul]
  simp_rw [mul_comm _ d]
  rw [integral_mul_left_eq_self G d]
  rfl

def slice (Φ : (Fin 2 → 𝔸[K]) → ℂ) (g : GL (Fin 2) 𝔸[K]) : 𝔸[K] → ℂ :=
  fun t ↦ Φ (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) 𝔸[K]))

theorem slice_mem {Φ : (Fin 2 → 𝔸[K]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 K) (g : GL (Fin 2) 𝔸[K]) :
    slice Φ g ∈ schwartzBruhat K :=
  slice_mem_schwartzBruhat (rightTranslate_mem_schwartzBruhat2 g hΦ)

def godementSection (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (Φ : (Fin 2 → 𝔸[K]) → ℂ)
    (g : GL (Fin 2) 𝔸[K]) : ℂ :=
  (χ₁.toIdele (detI g) : ℂ) * modPow (detI g) s * globalZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)

theorem two_mul_re (s : ℂ) : (2 * s).re = 2 * s.re := by simp

theorem integrable_godementIntegrand (χ₁ χ₂ : HeckeCharacter K) {s : ℂ} (hs : 1 < 2 * s.re)
    {Φ : (Fin 2 → 𝔸[K]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 K) (g : GL (Fin 2) 𝔸[K]) :
    Integrable (fun t : IdeleGroup K ↦
      slice Φ g t * ((χ₁ * χ₂⁻¹).toIdele t : ℂ) * ((ideleModule K t : ℝ) : ℂ) ^ (2 * s))
        (ideleMeasure K) :=
  integrable_globalZetaIntegrand (slice_mem hΦ g) _ (by rw [two_mul_re]; exact hs)

theorem slice_borelElt_mul (Φ : (Fin 2 → 𝔸[K]) → ℂ) (a d : IdeleGroup K) (x : 𝔸[K])
    (g : GL (Fin 2) 𝔸[K]) :
    slice Φ (borelElt a d x * g) = fun t ↦ slice Φ g (t * (d : 𝔸[K])) := by
  funext t
  simp only [slice, Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_borelElt]

theorem godementSection_borelElt_mul (χ₁ χ₂ : HeckeCharacter K) (s : ℂ)
    (Φ : (Fin 2 → 𝔸[K]) → ℂ) (a d : IdeleGroup K) (x : 𝔸[K]) (g : GL (Fin 2) 𝔸[K]) :
    godementSection χ₁ χ₂ s Φ (borelElt a d x * g) =
      (χ₁.toIdele a : ℂ) * (χ₂.toIdele d : ℂ) * modPow a s * modPow d (-s) *
        godementSection χ₁ χ₂ s Φ g := by
  simp only [godementSection, slice_borelElt_mul, globalZeta_mul_right, det_borelElt,
    map_mul, modPow_mul]
  have hμ : (((χ₁ * χ₂⁻¹).toIdele d)⁻¹ : Circle) = (χ₁.toIdele d)⁻¹ * χ₂.toIdele d := by
    change ((χ₁ (IdeleClassGroup.mk K d) * (χ₂ (IdeleClassGroup.mk K d))⁻¹)⁻¹ : Circle) = _
    rw [mul_inv, inv_inv]; rfl
  have h1 : modPow d s * modPow d (-(2 * s)) = modPow d (-s) := by
    rw [← modPow_add]; congr 1; ring
  have h2 : (χ₁.toIdele d : ℂ) * (((χ₁.toIdele d)⁻¹ : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  rw [hμ, Circle.coe_mul, ← h1]
  simp only [Circle.coe_mul]
  linear_combination (χ₁.toIdele a : ℂ) * (χ₂.toIdele d : ℂ) * modPow a s * modPow d s *
    modPow d (-(2 * s)) * (χ₁.toIdele (detI g) : ℂ) * modPow (detI g) s *
    globalZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) * h2

theorem godementSection_mem_principalSeries (χ₁ χ₂ : HeckeCharacter K) (s : ℂ)
    (Φ : (Fin 2 → 𝔸[K]) → ℂ) :
    godementSection χ₁ χ₂ s Φ ∈ principalSeries χ₁ χ₂ s :=
  fun a d x g ↦ godementSection_borelElt_mul χ₁ χ₂ s Φ a d x g

theorem godementSection_add (χ₁ χ₂ : HeckeCharacter K) {s : ℂ} (hs : 1 < 2 * s.re)
    {Φ Ψ : (Fin 2 → 𝔸[K]) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 K) (hΨ : Ψ ∈ schwartzBruhat2 K) :
    godementSection χ₁ χ₂ s (Φ + Ψ) = godementSection χ₁ χ₂ s Φ + godementSection χ₁ χ₂ s Ψ := by
  funext g
  have hZ : globalZeta (slice (Φ + Ψ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      globalZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) + globalZeta (slice Ψ g) (χ₁ * χ₂⁻¹) (2 * s) := by
    simp only [globalZeta]
    rw [← integral_add (integrable_godementIntegrand χ₁ χ₂ hs hΦ g)
      (integrable_godementIntegrand χ₁ χ₂ hs hΨ g)]
    congr 1
    funext t
    simp only [slice, Pi.add_apply]
    ring
  simp only [godementSection, Pi.add_apply, hZ]
  ring

theorem godementSection_smul (χ₁ χ₂ : HeckeCharacter K) (s : ℂ) (c : ℂ)
    (Φ : (Fin 2 → 𝔸[K]) → ℂ) :
    godementSection χ₁ χ₂ s (c • Φ) = c • godementSection χ₁ χ₂ s Φ := by
  funext g
  have hZ : globalZeta (slice (c • Φ) g) (χ₁ * χ₂⁻¹) (2 * s) =
      c * globalZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s) := by
    simp only [globalZeta]
    rw [← integral_const_mul]
    congr 1
    funext t
    simp only [slice, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [godementSection, Pi.smul_apply, smul_eq_mul, hZ]
  ring

def godementMap (χ₁ χ₂ : HeckeCharacter K) {s : ℂ} (hs : 1 < 2 * s.re) :
    schwartzBruhat2 K →ₗ[ℂ] principalSeries χ₁ χ₂ s where
  toFun Φ := ⟨godementSection χ₁ χ₂ s Φ, godementSection_mem_principalSeries χ₁ χ₂ s Φ⟩
  map_add' Φ Ψ := Subtype.ext (godementSection_add χ₁ χ₂ hs Φ.2 Ψ.2)
  map_smul' c Φ := Subtype.ext (godementSection_smul χ₁ χ₂ s c Φ)

end

end GroundTheory.Automorphic.GodementSection
