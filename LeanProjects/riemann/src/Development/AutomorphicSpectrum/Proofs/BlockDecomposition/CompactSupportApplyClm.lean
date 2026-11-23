import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnFderivApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RdSkewEqConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirRightLaplacianFormula

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobSecK

variable {n : ℕ}

theorem far_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Mat n) {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) : ∀ y ∈ GLs n, R < lg y → Rd X f y = 0 := by
  intro y hy hl
  simp only [Rd]
  rw [RCalc.ByParts.fderiv_eq_zero_far GlobalTheory.CompanionTheory.LengthGL.lgFacts hR hy hl]
  rfl

theorem cpt_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X : Mat n) {f : Mat n → V} (hc : Cpt f) :
    Cpt (Rd X f) :=
  hc.imp fun _ h => far_Rd X h

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem integrable_of_cpt {W : Type} [NormedAddCommGroup W] {h : Mat n → W} (hc : ContinuousOn h (GLs n))
    (hz : Cpt h) : Integrable (fun y : G n => h y.val) μ := by
  obtain ⟨R, hR⟩ := hz
  have hcont : Continuous fun y : G n => h y.val :=
    hc.comp_continuous Units.continuous_val fun y => RCalc.ByParts.val_mem_GLs y
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro
    ((GlobalTheory.CompanionTheory.LengthGL.lgFacts n).2.2.2.2.1 R) fun y hy => ?_)
  exact hR _ (RCalc.ByParts.val_mem_GLs y) (not_le.1 hy)

end Int

section Space

variable (n) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def Sp : Submodule ℂ (Mat n → V) where
  carrier := {f | ContDiffOn ℝ ∞ f (GLs n) ∧ Cpt f ∧ ∀ y, y ∉ GLs n → f y = 0}
  add_mem' := by
    rintro f h ⟨f1, ⟨R, f2⟩, f3⟩ ⟨h1, ⟨R', h2⟩, h3⟩
    refine ⟨f1.add h1, ⟨max R R', fun y hy hl => ?_⟩, fun y hy => ?_⟩
    · simp [f2 y hy (lt_of_le_of_lt (le_max_left _ _) hl), h2 y hy (lt_of_le_of_lt (le_max_right _ _) hl)]
    · simp [f3 y hy, h3 y hy]
  zero_mem' := ⟨contDiffOn_const, ⟨0, fun _ _ _ => rfl⟩, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨f1, ⟨R, f2⟩, f3⟩
    refine ⟨f1.const_smul c, ⟨R, fun y hy hl => ?_⟩, fun y hy => ?_⟩
    · simp [f2 y hy hl]
    · simp [f3 y hy]

variable {n V}
variable [MeasurableSpace (G n)]

def Hs (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Type := Sp n V

variable (μ : Measure (G n))

instance : AddCommGroup (Hs μ V) := inferInstanceAs (AddCommGroup (Sp n V))
instance : Module ℂ (Hs μ V) := inferInstanceAs (Module ℂ (Sp n V))

variable {μ}

def Hs.fn (f : Hs μ V) : Mat n → V := Subtype.val (p := fun f => f ∈ Sp n V) f

theorem Hs.smooth (f : Hs μ V) : ContDiffOn ℝ ∞ f.fn (GLs n) := f.2.1
theorem Hs.cpt (f : Hs μ V) : Cpt f.fn := f.2.2.1
theorem Hs.off (f : Hs μ V) {y : Mat n} (hy : y ∉ GLs n) : f.fn y = 0 := f.2.2.2 y hy
@[simp] theorem Hs.add_fn (f h : Hs μ V) : (f + h).fn = f.fn + h.fn := rfl
@[simp] theorem Hs.smul_fn (c : ℂ) (f : Hs μ V) : (c • f).fn = c • f.fn := rfl
@[simp] theorem Hs.zero_fn : (0 : Hs μ V).fn = 0 := rfl

theorem Hs.ext_on {f h : Hs μ V} (e : Set.EqOn f.fn h.fn (GLs n)) : f = h := by
  apply Subtype.ext
  funext y
  by_cases hy : y ∈ GLs n
  · exact e hy
  · exact (f.off hy).trans (h.off hy).symm

def toH (μ : Measure (G n)) (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hc : Cpt f) : Hs μ V :=
  ⟨(GLs n).indicator f, hf.congr fun y hy => Set.indicator_of_mem hy f,
    hc.imp fun _ h y hy hl => (Set.indicator_of_mem hy f).trans (h y hy hl),
    fun _ hy => Set.indicator_of_notMem hy f⟩

theorem toH_fn {f : Mat n → V} {hf : ContDiffOn ℝ ∞ f (GLs n)} {hc : Cpt f} {y : Mat n} (hy : y ∈ GLs n) :
    (toH μ f hf hc).fn y = f y :=
  Set.indicator_of_mem hy f

end Space

section Inner

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem Hs.continuous_val (f : Hs μ V) : Continuous fun y : G n => f.fn y.val :=
  f.smooth.continuousOn.comp_continuous Units.continuous_val fun y => RCalc.ByParts.val_mem_GLs y

theorem integrable_inner (f h : Hs μ V) : Integrable (fun y : G n => ⟪f.fn y.val, h.fn y.val⟫_ℂ) μ := by
  obtain ⟨R, hR⟩ := f.cpt
  refine integrable_of_cpt μ (h := fun y => ⟪f.fn y, h.fn y⟫_ℂ)
    (f.smooth.continuousOn.inner h.smooth.continuousOn) ⟨R, fun y hy hl => ?_⟩
  simp [hR y hy hl]

theorem ip_self (f : Hs μ V) : ip μ f.fn f.fn = ((∫ y : G n, ‖f.fn y.val‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp only [ip, inner_self_eq_norm_sq_to_K]
  rw [← integral_complex_ofReal]
  simp

instance core : InnerProductSpace.Core ℂ (Hs μ V) where
  inner f h := ip μ f.fn h.fn
  conj_inner_symm f h := by
    simp only [ip]
    rw [← integral_conj]
    simp
  re_inner_nonneg f := by
    show 0 ≤ RCLike.re (ip μ f.fn f.fn)
    rw [ip_self]
    simpa using integral_nonneg fun y : G n => by positivity
  add_left f g h := by
    simp only [ip, Hs.add_fn, Pi.add_apply, inner_add_left]
    exact integral_add (integrable_inner f h) (integrable_inner g h)
  smul_left f h c := by
    simp only [ip, Hs.smul_fn, Pi.smul_apply, inner_smul_left]
    exact integral_const_mul _ _
  definite f hf := by
    have h0 : ∫ y : G n, ‖f.fn y.val‖ ^ 2 ∂μ = 0 := by
      have : ip μ f.fn f.fn = 0 := hf
      rw [ip_self] at this
      exact_mod_cast this
    have hint : Integrable (fun y : G n => ‖f.fn y.val‖ ^ 2) μ := by
      obtain ⟨R, hR⟩ := f.cpt
      refine integrable_of_cpt μ (h := fun y => ‖f.fn y‖ ^ 2) (f.smooth.continuousOn.norm.pow 2) ⟨R, fun y hy hl => ?_⟩
      simp [hR y hy hl]
    have h1 := (integral_eq_zero_iff_of_nonneg (fun y : G n => by positivity) hint).1 h0
    have hc : Continuous fun y : G n => ‖f.fn y.val‖ ^ 2 := (f.continuous_val.norm).pow 2
    have h2 := (Continuous.ae_eq_iff_eq μ hc continuous_const (g := fun _ => (0 : ℝ))).1 h1
    refine Hs.ext_on fun y hy => ?_
    have h3 := congrFun h2 (RCalc.ByParts.toG hy)
    simpa using h3

instance : NormedAddCommGroup (Hs μ V) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
instance : InnerProductSpace ℂ (Hs μ V) := InnerProductSpace.ofCore core.toCore

end Inner

section Ops

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [MeasurableSpace (G n)]
variable (μ : Measure (G n))

def Xop (p : Ix n) : Module.End ℂ (Hs μ V) where
  toFun f := toH μ (Rd (bs p) f.fn) (RCalc.Rd_contDiffOn _ f.smooth) (cpt_Rd _ f.cpt)
  map_add' f h := Hs.ext_on fun y hy => by
    simp only [Hs.add_fn, Pi.add_apply, toH_fn hy]
    exact OmDec.Rd_add_right _ f.smooth h.smooth hy
  map_smul' c f := Hs.ext_on fun y hy => by
    simp only [Hs.smul_fn, Pi.smul_apply, toH_fn hy, RingHom.id_apply]
    exact OmDec.Rd_smul_right _ _ f.smooth hy

variable {μ}

variable (μ)

def Lh : Module.End ℂ (Hs μ V) := -∑ p : Ix n, Xop μ p * Xop μ p

variable {μ} in
theorem smooth_alt (T : V →L[ℂ] V) (f : Hs μ V) : ContDiffOn ℝ ∞ (fun y => T (f.fn y)) (GLs n) :=
  (T.restrictScalars ℝ).contDiff.comp_contDiffOn f.smooth

variable {μ} in
theorem compact_support_apply_clm (T : V →L[ℂ] V) (f : Hs μ V) : Cpt (fun y => T (f.fn y)) :=
  f.cpt.imp fun _ h y hy hl => by show T (f.fn y) = 0; rw [h y hy hl, map_zero]

def Tm (T : V →L[ℂ] V) : Module.End ℂ (Hs μ V) where
  toFun f := toH μ (fun y => T (f.fn y)) (smooth_alt T f) (compact_support_apply_clm T f)
  map_add' f h := Hs.ext_on fun y hy => by
    simp only [Hs.add_fn, Pi.add_apply]
    rw [toH_fn hy, toH_fn hy, toH_fn hy]
    simp only [Hs.add_fn, Pi.add_apply, map_add]
  map_smul' c f := Hs.ext_on fun y hy => by
    simp only [Hs.smul_fn, Pi.smul_apply, RingHom.id_apply]
    rw [toH_fn hy, toH_fn hy]
    simp only [Hs.smul_fn, Pi.smul_apply, map_smul]

variable {μ}

end Ops

end GlobalTheory.CompanionTheory.SobSecK
