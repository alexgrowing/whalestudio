import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

namespace EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.CompanionTheory.FiniteVanish

end GlobalTheory.CompanionTheory.FiniteVanish

end

end EqZeroOfFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio
theorem _root_.GlobalTheory.Adopt.continuous_automorphic_eq_zero_of_vanish_on_finiteAdelic : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), (∀ τ, (gramAt D V τ).PosDef) → Continuous φ → (∀ γ ∈ GQ V, ∀ h, φ (γ * h) = φ h) → (∀ h ∈ GfC V, φ h = 0) → ∀ h, φ h = 0 := by
  intro D V φ _ hcont hleft hzero g
  haveI := GlobalTheory.AutFunCounterexample.topGroup_GA D V
  obtain ⟨u, hu, f, hf, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D V).1 g

  set ψ : GA D V → ℂ := fun x => φ (x * f) with hψ
  have hψc : Continuous ψ := hcont.comp (continuous_mul_right f)
  have hvan : ∀ γ ∈ GQ V, ∀ k ∈ GfC V, ψ (γ * k) = 0 := fun γ hγ k hk => by
    simp only [hψ, mul_assoc, hleft γ hγ]
    exact hzero _ ((GfC V).mul_mem hk hf)
  show ψ u = 0
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hin, -⟩ :=
    GlobalTheory.RealApprox.weak_approx_real V u hu {x | ψ x ≠ 0} (isOpen_ne_fun hψc continuous_const) hne
  exact hin (hvan γ hγ k hk)

end
