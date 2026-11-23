import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SmoothDecompositionForms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousRepSmoothOnUH
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CasimirEigenvalueCoefficients
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.HeckeMultiplication

open Matrix Finset PI.UpqRep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.TensCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms (HRep IsSmoothMap IsSmoothMapInto IsSmoothMapFrom IsSmoothDecomp IsSignedDecomp IsFormRep
  tensSmooth tensAct tensForm pureT contr LieWord Mx Ix)

variable {k r : ℕ}

def toRep (R : HRep k r) : BranchingSupport.Rep k r where
  H := R.H
  σ := R.σ

def repEquiv (k r : ℕ) : HRep k r ≃ {R : BranchingSupport.Rep k r // IsURepOn (BranchingSupport.GG k r) R.σ} where
  toFun R := ⟨toRep R, R.isURep⟩
  invFun R := { H := R.1.H, σ := R.1.σ, isURep := R.2 }
  left_inv _ := rfl
  right_inv _ := rfl

theorem isURepOn_of_isDS {R : BranchingSupport.Rep k r} {ε : Ix k r → Bool} {μ : Ix k r → ℝ} (h : R.IsDS ε μ) :
    IsURepOn (BranchingSupport.GG k r) R.σ := by
  obtain ⟨-, P, hP, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨⟨by simpa [hPP] using h1, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · have := hm _ (hmaps ha) _ (hmaps hb)
    have e2 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    simpa only [e2, e] using this
  · simpa only [e] using hn _ (hmaps hg) v
  · have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp h3.continuousOn hmaps
    simpa only [Function.comp_def, e] using this

def dsEquiv (ε : Ix k r → Bool) (μ : Ix k r → ℝ) :
    {R : HRep k r // R.IsDiscrete ε μ} ≃ {R : BranchingSupport.Rep k r // R.IsDS ε μ} where
  toFun R := ⟨toRep R.1, R.2⟩
  invFun R := ⟨{ H := R.1.H, σ := R.1.σ, isURep := isURepOn_of_isDS R.2 }, R.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smul_mem (R : HRep k r) (a : ℂ) {v : R.H} (hv : v ∈ R.smooth) : a • v ∈ R.smooth :=
  Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv

end Smooth

section Tensor

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem single_mem (R : HRep k r) (c : ι) {v : R.H} (hv : v ∈ R.smooth) : Pi.single c v ∈ tensSmooth ι R := by
  intro d
  by_cases h : d = c
  · subst h; simpa using hv
  · simpa [Pi.single_eq_of_ne h] using GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms.zero_mem_smooth R

def sumOf {E E' : Type} [AddCommMonoid E'] (P : ι → E → E') (x : ι → E) : E' := ∑ c, P c (x c)

def compOf {E E' : Type} [Zero E] (A : (ι → E) → E') (c : ι) (v : E) : E' := A (Pi.single c v)

def Linked (R R' : HRep k r) (P : ι → R.H → R'.H) (A : (ι → R.H) → R'.H) : Prop :=
  (∀ c, P c 0 = 0) ∧ ∀ x ∈ tensSmooth ι R, A x = ∑ c, P c (x c)

theorem Linked.comp {R R' : HRep k r} {P : ι → R.H → R'.H} {A : (ι → R.H) → R'.H} (h : Linked R R' P A) (c : ι)
    {v : R.H} (hv : v ∈ R.smooth) : P c v = A (Pi.single c v) := by
  rw [h.2 _ (single_mem R c hv), Finset.sum_eq_single c (fun d _ hd => by simp [Pi.single_eq_of_ne hd, h.1])
    (by simp)]
  simp

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : HRep k r} {Rs : κ → HRep k r}
  {io : ∀ I, (Rs I).H → ι → R.H} {pr : ∀ I, ι → R.H → (Rs I).H} {p : ∀ I, (ι → R.H) → (Rs I).H} {ep : κ → ℝ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem continuousOn_of_smoothOnH {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : SmoothOnH H f) : ContinuousOn f (UH H) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hag⟩ := hf g₀ hg₀
  have h1 : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg)
  refine h1.continuousWithinAt.congr_of_eventuallyEq ?_ (hag g₀ hg hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg), self_mem_nhdsWithin] with g h1 h2
  exact hag g h1 h2

end Tensor

end GlobalTheory.TensCompare

end
