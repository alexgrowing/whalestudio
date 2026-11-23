import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.BorelTup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.THeisK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Tunit
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open PositivityTheory.SiegelWeilFormula.TBij.Adp PositivityTheory.SiegelWeilFormula.KTunit
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
theorem tUnit_k : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k := by
  intro F E _ _ _ _ _ σ d ν hν x Φ hΦ Φ' hΦ'
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tunit.T_chart_k d
  have hpres : ∀ φ ∈ schA F d.κ, d.om x φ ∈ schA F d.κ := fun φ hφ => d.ok.dbl.weil.2.1.pres x φ hφ
  have hunit := d.ok.dbl.weil.2.1.unit
  obtain ⟨hμ, hint⟩ := _root_.PositivityTheory.SiegelWeilFormula.KTunit.map_haar_k d τ ν hν
  set μ := ν.map (_root_.PositivityTheory.SiegelWeilFormula.KTunit.cmap_k d τ) with hμdef
  have h1 : ∀ Ψ ∈ d.sch, ∀ Ψ' ∈ d.sch, ∫ X, d.T Ψ X * star (d.T Ψ' X) ∂ν =
      (C * star C) * ∫ y, S0 Ψ y * star (S0 Ψ' y) ∂μ := by
    intro Ψ hΨ Ψ' hΨ'
    rw [← integral_const_mul, ← hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hT _ hΨ, hT _ hΨ', star_mul']
    change _ = C * star C * (S0 Ψ (fun k => d.crd X (τ k)) * star (S0 Ψ' fun k => d.crd X (τ k)))
    ring
  rw [h1 _ (hpres Φ hΦ) _ (hpres Φ' hΦ'), h1 _ hΦ _ hΦ']
  congr 1
  obtain ⟨c, hc0, hctop, hcn⟩ := hop.norm μ μ hμ hμ
  have hp' : ∀ φ ∈ schA F d.κ, (S0 ∘ₗ d.om x ∘ₗ S0') φ ∈ schA F d.κ := fun φ hφ =>
    hop.pres _ (hpres _ (hop.pres' φ hφ))
  have hT' : ∀ φ ∈ schA F d.κ, ∫⁻ y, ‖(S0 ∘ₗ d.om x ∘ₗ S0') φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
    intro φ hφ
    have e1 := hcn _ (hpres _ (hop.pres' φ hφ))
    have e2 := hcn _ (hop.pres' φ hφ)
    rw [hop.right φ hφ] at e2
    have e3 := hunit μ hμ x _ (hop.pres' φ hφ)
    simp only [LinearMap.comp_apply]
    rw [e1, e2, e3]
  have := GlobalTheory.DblUnitaryBox.integral_mul_star_eq μ hμ (S0 ∘ₗ d.om x ∘ₗ S0') hp' hT' (hop.pres Φ hΦ) (hop.pres Φ' hΦ')
  simpa only [LinearMap.comp_apply, hop.left _ hΦ, hop.left _ hΦ'] using this
end PositivityTheory.SiegelWeilFormula.Tunit
end
end
