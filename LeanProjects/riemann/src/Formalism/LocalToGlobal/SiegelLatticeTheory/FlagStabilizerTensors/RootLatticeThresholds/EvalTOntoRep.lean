import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTReg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ExplicitFormulaBoundHolds

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.RowDict Formalism.MainNotions.LeviCoordinates

namespace Formalism.L2.SG.EvalTOntoRep

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def IsContRep (f : L2X X) (φ : X.B.I.GA → ℂ) : Prop :=
  Continuous φ ∧ (∀ γ ∈ X.B.I.GFset, ∀ y, φ (γ * y) = φ y) ∧ ((f : X.B.I.GA → ℂ) =ᵐ[muX X] φ)

theorem eq_zero_of_ae (ψ : X.B.I.GA → ℂ) (hc : Continuous ψ) (hinv : ∀ γ ∈ X.B.I.GFset, ∀ y, ψ (γ * y) = ψ y)
    (h0 : ψ =ᵐ[muX X] 0) : ψ = 0 := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.L2.SG.Count.muA_isHaar X.B.I X.B.μf
  have := rr_muA_left X.B.I X.B.μf
  set N : Set X.B.I.GA := {y | ψ y ≠ 0} with hNd
  have hN : IsOpen N := isOpen_ne_fun hc continuous_const
  have hfm : MeasurableSet X.B.fund := X.B.fund_spec.1
  have h1 : X.B.I.muA X.B.μf (N ∩ X.B.fund) = 0 := by
    have h0' : ∀ᵐ y ∂(X.B.I.muA X.B.μf), y ∈ X.B.fund → ψ y = 0 := by
      rw [← ae_restrict_iff' hfm]
      exact h0
    rw [ae_iff] at h0'
    refine measure_mono_null (fun y hy => ?_) h0'
    simp only [Set.mem_setOf_eq, Classical.not_imp]
    exact ⟨hy.2, hy.1⟩
  have hsub : N ⊆ ⋃ γ : rr_GF X.B.I, (fun y => (γ : X.B.I.GA) * y) ⁻¹' (N ∩ X.B.fund) := by
    intro y hy
    obtain ⟨γ, hγ, hγy⟩ := X.B.fund_spec.2.1 y
    refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_⟩
    refine ⟨?_, hγy⟩
    show ψ (γ * y) ≠ 0
    rw [hinv γ hγ y]
    exact hy
  have h2 : X.B.I.muA X.B.μf N = 0 := by
    refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
    rw [measure_preimage_mul]
    exact h1
  have h3 : N = ∅ := (hN.measure_eq_zero_iff (X.B.I.muA X.B.μf)).1 h2
  funext y
  by_contra hne
  have : y ∈ N := hne
  rw [h3] at this
  exact this

theorem contRep_unique {f : L2X X} {φ φ' : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X f φ') : φ = φ' := by
  have e := eq_zero_of_ae X (fun y => φ y - φ' y) (h.1.sub h'.1)
    (fun γ hγ y => by simp only [h.2.1 γ hγ y, h'.2.1 γ hγ y])
    ((h.2.2.symm.trans h'.2.2).mono fun y hy => by simp [hy])
  funext y
  exact sub_eq_zero.1 (congrFun e y)

theorem contRep_add {f g : L2X X} {φ ψ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (h' : IsContRep X g ψ) :
    IsContRep X (f + g) (φ + ψ) :=
  ⟨h.1.add h'.1, fun γ hγ y => by simp [h.2.1 γ hγ y, h'.2.1 γ hγ y],
    (Lp.coeFn_add f g).trans (h.2.2.add h'.2.2)⟩

theorem contRep_smul (a : ℂ) {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) :
    IsContRep X (a • f) (a • φ) :=
  ⟨h.1.const_smul a, fun γ hγ y => by simp [h.2.1 γ hγ y], (Lp.coeFn_smul a f).trans (h.2.2.const_smul a)⟩

theorem contRep_zero : IsContRep X 0 0 :=
  ⟨continuous_const, fun _ _ _ => rfl, Lp.coeFn_zero ℂ 2 (muX X)⟩

theorem contRep_reg {f : L2X X} {φ : X.B.I.GA → ℂ} (h : IsContRep X f φ) (y : X.B.I.GA) :
    IsContRep X (X.B.R y f) (fun x => φ (x * y)) := by
  have hm : MemLp φ 2 (muX X) := (Lp.memLp f).ae_eq h.2.2
  have ef : f = hm.toLp φ := Lp.ext (h.2.2.trans hm.coeFn_toLp.symm)
  refine ⟨h.1.comp (continuous_mul_right y), fun γ hγ x => by simp only [mul_assoc, h.2.1 γ hγ], ?_⟩
  rw [ef]
  exact Formalism.L2.SG.EvalTReg.reg_toLp_X X φ h.2.1 hm y

end Formalism.L2.SG.EvalTOntoRep

end
