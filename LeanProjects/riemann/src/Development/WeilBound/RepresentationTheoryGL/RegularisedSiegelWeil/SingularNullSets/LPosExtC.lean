import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LPosExtA
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open Set MeasureTheory CompactlySupported

namespace PositivityTheory.Rg.Rsw.L.LPosExt

variable {X : Type} [TopologicalSpace X]

def AR (A : Submodule ℂ (X → ℂ)) : Submodule ℝ (X → ℂ) where
  carrier := {f | f ∈ A ∧ ∀ x, (f x).im = 0}
  add_mem' := fun ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨A.add_mem ha hb, fun x => by simp [ha' x, hb' x]⟩
  zero_mem' := ⟨A.zero_mem, fun x => by simp⟩
  smul_mem' c f := fun ⟨hf, hf'⟩ => ⟨by
      have : c • f = (c : ℂ) • f := by ext x; simp [Complex.real_smul]
      rw [this]; exact A.smul_mem _ hf, fun x => by simp [hf' x]⟩

def reC (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    AR A →ₗ[ℝ] C_c(X, ℝ) where
  toFun f := ⟨⟨fun x => (f.1 x).re, Complex.continuous_re.comp (hA _ f.2.1).1⟩,
    (hA _ f.2.1).2.comp_left Complex.zero_re⟩
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

theorem reC_inj (A : Submodule ℂ (X → ℂ)) (hA : ∀ f ∈ A, Continuous f ∧ HasCompactSupport f) :
    Function.Injective (reC A hA) := by
  intro f g hfg
  apply Subtype.ext
  funext x
  have h := congrArg (fun u : C_c(X, ℝ) => u x) hfg
  simp only [reC, LinearMap.coe_mk, AddHom.coe_mk] at h
  exact Complex.ext h ((f.2.2 x).trans (g.2.2 x).symm)

def reL (A : Submodule ℂ (X → ℂ)) (L : A →ₗ[ℂ] ℂ) : AR A →ₗ[ℝ] ℝ where
  toFun f := (L ⟨f.1, f.2.1⟩).re
  map_add' f g := by
    have : (⟨(f + g).1, (f + g).2.1⟩ : A) = ⟨f.1, f.2.1⟩ + ⟨g.1, g.2.1⟩ := rfl
    simp only [this, map_add, Complex.add_re]
  map_smul' c f := by
    have : (⟨(c • f).1, (c • f).2.1⟩ : A) = (c : ℂ) • ⟨f.1, f.2.1⟩ := by
      apply Subtype.ext; ext x; simp [Complex.real_smul]
    simp only [this, map_smul, smul_eq_mul, Complex.re_ofReal_mul, RingHom.id_apply]

theorem dom (A : Submodule ℂ (X → ℂ))
    (hbump : ∀ C, IsCompact C → ∃ f ∈ A, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) ∧ ∀ x ∈ C, f x = 1)
    {y : X → ℝ} (hy : Continuous y) (hyc : HasCompactSupport y) :
    ∃ b ∈ A, (∀ x, 0 ≤ (b x).re ∧ (b x).im = 0) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x, 0 ≤ M * (b x).re + y x ∧ 0 ≤ M * (b x).re - y x := by
  obtain ⟨b, hbA, hb0, hb1⟩ := hbump (tsupport y) hyc
  obtain ⟨C, hC⟩ := hy.bounded_above_of_compact_support hyc
  refine ⟨b, hbA, hb0, max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport y
  · rw [hb1 x hx, Complex.one_re, mul_one]
    have := hC x
    rw [Real.norm_eq_abs] at this
    constructor <;> linarith [abs_le.mp this, le_max_left C 0]
  · rw [image_eq_zero_of_notMem_tsupport hx]
    have := mul_nonneg (le_max_right C 0) (hb0 x).1
    constructor <;> linarith

end PositivityTheory.Rg.Rsw.L.LPosExt
