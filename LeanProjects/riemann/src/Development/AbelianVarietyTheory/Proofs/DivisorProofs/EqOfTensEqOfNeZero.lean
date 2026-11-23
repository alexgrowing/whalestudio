import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvZeroFinLoc

theorem eq_of_tens_eq_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r ≠ 0)
    (g h : (κ → Fv F v) → ℂ) (e : tens (evFin F v) g r = tens (evFin F v) h r) : g = h := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp h0
  funext ξ
  set z : κ → AF F := fun k => GlobalTheory.LatVac.liftV v (ξ k - evFin F v (x₀ k)) with hz
  have hzat : At (evFin F v) z := by
    intro u hu
    funext k
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hevx : (fun i => evFin F v ((x₀ + z) i)) = ξ := by
    funext i
    simp [hz, GlobalTheory.LatVac.evFin_liftV]
  have hrx : r (x₀ + z) = r x₀ := hr x₀ z hzat
  have := congrFun e (x₀ + z)
  simp only [tens, hevx, hrx] at this
  exact mul_right_cancel₀ (by simpa using hx₀) this

end GlobalTheory.ThK.EvZeroFinLoc

end
