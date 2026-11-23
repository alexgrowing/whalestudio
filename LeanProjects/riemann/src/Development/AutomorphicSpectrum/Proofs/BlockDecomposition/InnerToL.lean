import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.WaveCp

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Ld (X : Mat n) (f : Mat n → V) : Mat n → V := fun g => fderiv ℝ f g (X * g)

def Lw (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) : Mat n → V :=
  w.foldr (fun p h => Ld (bs p) h) f

@[simp] theorem Lw_nil (f : Mat n → V) : Lw [] f = f := rfl

theorem Lw_cons (p : Bool × Fin n × Fin n) (w : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Lw (p :: w) f = Ld (bs p) (Lw w f) := rfl

def transl (x : G n) (f : Mat n → V) : Mat n → V := fun g => f ((x⁻¹ : G n).val * g)

def Ac (c : ℝ) (f : Mat n → V) : Mat n → V := (c : ℂ) • f - Om f

end Ops

def DS (E : KMod n) : Submodule ℂ (Mat n → E.V) where
  carrier := {f | f ∈ CE E ∧ Cpt f}
  add_mem' := by
    rintro f h ⟨⟨hf, hf'⟩, R, hR⟩ ⟨⟨hh, hh'⟩, S, hS⟩
    refine ⟨⟨hf.add hh, fun g hg k => ?_⟩, max R S, fun y hy hl => ?_⟩
    · simp [hf' g hg k, hh' g hg k]
    · simp [hR y hy (lt_of_le_of_lt (le_max_left _ _) hl), hS y hy (lt_of_le_of_lt (le_max_right _ _) hl)]
  zero_mem' := by
    refine ⟨⟨contDiffOn_const, fun g _ k => ?_⟩, 0, fun y _ _ => rfl⟩
    simp
  smul_mem' := by
    rintro a f ⟨⟨hf, hf'⟩, R, hR⟩
    refine ⟨⟨contDiffOn_const.smul hf, fun g hg k => ?_⟩, R, fun y hy hl => ?_⟩
    · simp [hf' g hg k]
    · simp [hR y hy hl]

section L2

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [MeasurableSpace (G n)]

def toL (μ : Measure (G n)) (f : Mat n → V) : Lp V 2 μ :=
  open Classical in if h : MemLp (fun y : G n => f y.val) 2 μ then h.toLp _ else 0

def IsRep (μ : Measure (G n)) (b : Mat n → V) (y : Lp V 2 μ) : Prop :=
  (y : G n → V) =ᵐ[μ] fun g => b g.val

theorem toL_coe {μ : Measure (G n)} {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    IsRep μ f (toL μ f) := by
  unfold IsRep toL
  rw [dif_pos h]
  exact h.coeFn_toLp

variable [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def LT (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => x⁻¹ * g) (measurePreserving_mul_left μ x⁻¹)).toContinuousLinearMap

def RK [μ.IsMulRightInvariant] (E : KMod n) (k : Matrix.unitaryGroup (Fin n) ℂ) : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ :=
  (ContinuousLinearMap.compLpL 2 μ (E.ρ k)).comp
    (Lp.compMeasurePreservingₗᵢ ℂ (fun g : G n => g * (Unitary.toUnits k : G n))
      (measurePreserving_mul_right μ (Unitary.toUnits k : G n))).toContinuousLinearMap

end L2

end GlobalTheory.CompanionTheory.WaveCp
