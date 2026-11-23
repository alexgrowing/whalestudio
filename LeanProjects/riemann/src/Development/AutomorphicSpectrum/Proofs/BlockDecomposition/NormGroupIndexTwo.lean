import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GaussLam

theorem localZeta_comp_norm_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E]
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E]
    [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (η : Fˣ →* ℂˣ) (hc : Continuous η)
    (hη : ∀ a : Fˣ, ((η a : ℂˣ) : ℂ) = nsg E (a : F)) (κ : ℝ) (hκ : FibProp F E κ) (f : F → ℂ)
    (hf : f ∈ schwartzBruhat F) :
    localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) =
      (κ / 2 : ℂ) * (localZeta f 1 (1 / 2) + localZeta f η (1 / 2)) := by
  classical
  set h : Fˣ → ℂ := fun a => f a * (((1 : Fˣ →* ℂˣ) a : ℂˣ) : ℂ) *
    ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hh
  set g : E → ℂ := fun x => f (Algebra.norm F x) *
    ((modulus (Algebra.norm F x) : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hg
  have hgu : (fun x : Eˣ => g x) = h ∘ normUnits F E := by
    funext x
    simp [hh, hg, coe_normUnits]
  have hcont : Continuous (fun x : Eˣ => g x) := by
    rw [hgu]
    exact (continuous_localZeta_integrand hf continuous_one (1 / 2)).comp
      (continuous_normUnits F E)
  have hinv : ∀ (x : E) (u : Eˣ), Algebra.norm F (u : E) = 1 → g (x * u) = g x := by
    intro x u hu
    simp only [hg, map_mul, hu, mul_one]
  have hL : localZeta (fun x : E => f (Algebra.norm F x)) 1 (1 / 2) = ∫ x : Eˣ, g x ∂multHaar E := by
    unfold localZeta
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hg, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E)]
  have hfib : ∀ a : Fˣ, nfib E g a =
      (1 / 2 : ℂ) * (h a + f a * ((η a : ℂˣ) : ℂ) * ((modulus (a : F) : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    intro a
    by_cases hr : ∃ t : Eˣ, Algebra.norm F (t : E) = (a : F)
    · have e1 : nfib E g a = g (hr.choose : E) := dif_pos hr
      have e2 : ((η a : ℂˣ) : ℂ) = 1 := by rw [hη, nsg, if_pos hr]
      rw [e1, e2]
      simp only [hg, hh, hr.choose_spec]
      simp
      ring
    · have e1 : nfib E g a = 0 := dif_neg hr
      have e2 : ((η a : ℂˣ) : ℂ) = -1 := by rw [hη, nsg, if_neg hr]
      rw [e1, e2]
      simp only [hh]
      simp
  have hexp1 : quasiCharExponent (1 : Fˣ →* ℂˣ) = 0 := by
    simp [quasiCharExponent]
  have hexpη : quasiCharExponent η = 0 := by
    have : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := by
      rw [hη, nsg]
      split_ifs <;> simp
    simp [quasiCharExponent, this]
  have hi1 := integrable_localZeta (s := 1 / 2) hf (continuous_one : Continuous (1 : Fˣ →* ℂˣ))
    (by rw [hexp1]; norm_num)
  have hi2 := integrable_localZeta (s := 1 / 2) hf hc (by rw [hexpη]; norm_num)
  rw [hL, (hκ g hcont hinv).2, integral_congr_ae (Filter.Eventually.of_forall hfib),
    integral_const_mul, integral_add hi1 hi2]
  unfold localZeta
  push_cast
  ring

end GlobalTheory.CompanionTheory.GaussLam
