import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTranslationCuspFormMapsEqSmoothLinearMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupVal

theorem tprod_ne_zero' {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_bound_half_lt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)), GlobalTheory.Unf.Vol V → ∀ t ∈ MultT θ M J 1, t ≠ 0 →
    ∀ w : M.Vec, (∀ τ, (w τ : M.H τ) ≠ 0) → ∃ b : ℝ, ∃ x : GA D V,
      (∀ h, ‖t (PiTensorProduct.tprod ℂ w) h‖ ≤ b) ∧ b / 2 < ‖t (PiTensorProduct.tprod ℂ w) x‖ := by
  intro hP D θ hθ V S M J vol t ht ht0 w hw
  have hw' : PiTensorProduct.tprod ℂ w ≠ 0 :=
    tprod_ne_zero' fun τ h => hw τ (by simp [h])
  have hS := GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D θ hθ V S M J 1 vol.μ vol.𝓕 vol.haar vol.fund
  set φ := t (PiTensorProduct.tprod ℂ w) with hφ
  have hφ0 : φ ≠ 0 := fun h => ht0 (GlobalTheory.T.multiplicitySpace_eq_zero_of_apply_nonzero_tensor_zero θ M J 1 vol.μ vol.𝓕 hθ vol.haar vol.fund hS t ht _ hw' h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  have hR := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J 1 t ht
    (PiTensorProduct.tprod ℂ w)).2.2
  obtain ⟨C, hC⟩ := hR.2.2 0
  have hbdd : BddAbove (Set.range fun g => ‖φ g‖) := ⟨C, by
    rintro _ ⟨g, rfl⟩
    simpa using hC g⟩
  have hle : ∀ h, ‖φ h‖ ≤ sSup (Set.range fun g => ‖φ g‖) := fun h => le_csSup hbdd ⟨h, rfl⟩
  have hpos : 0 < sSup (Set.range fun g => ‖φ g‖) := lt_of_lt_of_le (norm_pos_iff.2 hx₀) (hle x₀)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) (half_lt_self hpos)
  exact ⟨_, x, hle, hx⟩

end GlobalTheory.SupVal
