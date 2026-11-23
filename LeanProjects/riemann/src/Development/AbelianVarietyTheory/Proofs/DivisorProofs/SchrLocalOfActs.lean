import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictionAndProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchrodingerTensorEqLocalOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntAddConjEqOneOfBaseGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
open scoped GlobalTheory.VacAny

noncomputable section

theorem GlobalTheory.AdelicActs.schr_local_of_acts : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : Pl F) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), (∀ i, At (evFin F v) (w.1 i)) → (∀ i, At (evFin F v) (w.2 i)) →
    ∀ φ φ' : (κ → Fv F v) → ℂ, φ ∈ SB (κ → Fv F v) → Acts (evFin F v) (schr ψ w) φ φ' →
      schr (GlobalTheory.VacAny.psiV ψ v) (fun i => evFin F v (w.1 i), fun i => evFin F v (w.2 i)) φ = φ' := by
  intro F _ _ ψ v κ _ w h1 h2 φ φ' hφ hA
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  have e := hA r hr
  rw [GlobalTheory.SchrLoc.schr_tens_of_at ψ v w h1 h2 φ r hr.1] at e
  funext y
  let z : κ → AF F := fun i => GlobalTheory.EmbChart.atPlace v (y i - evFin F v (x₀ i))
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.VacAny.at_atPlace _
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hz
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [z, Pi.add_apply, map_add, GlobalTheory.EmbChart.evFin_atPlace, add_sub_cancel]
  have e2 := congrFun e (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at e2
  rw [hev, hrx] at e2
  exact mul_right_cancel₀ hx₀ e2
