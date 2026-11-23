import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem coord_mul_eq_sum (ε : Fin n → Bool) (c : Fin n × Fin n × Bool) (a k : KG ε) :
    coord ε c (a * k) = ∑ l : Fin n, coord ε (c.1, l, c.2.2) a * coord ε (l, c.2.1, c.2.2) k := by
  simp only [coord, toMK_mul, Matrix.mul_apply]
  split_ifs
  · rfl
  · rw [star_sum]; exact Finset.sum_congr rfl fun l _ => by rw [star_mul', mul_comm]

theorem integrable_muK_of_continuous {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    Integrable F (muK ε) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem conv_mono_mem (ε : Fin n → Bool) (s : List (Fin n × Fin n × Bool)) :
    ∀ (d : ℕ), s.length ≤ d → ∀ h : KG ε → ℂ, Continuous h →
      (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction s with
  | nil =>
    intro d _ h _
    simpa [mono] using const_mem ε d (∫ k, h k ∂(muK ε))
  | cons c s ih =>
    intro d hd h hh
    have hd' : s.length + 1 ≤ d := by simpa using hd
    have e : (fun k' : KG ε => ∫ k, mono ε (c :: s) (k'⁻¹ * k) * h k ∂(muK ε)) =
        ∑ l : Fin n, (fun k' : KG ε => coord ε (c.1, l, c.2.2) k'⁻¹) *
          (fun k' : KG ε => ∫ k, mono ε s (k'⁻¹ * k) * (coord ε (l, c.2.1, c.2.2) k * h k) ∂(muK ε)) := by
      funext k'
      simp only [Finset.sum_apply, Pi.mul_apply]
      simp only [← integral_const_mul]
      rw [← integral_finset_sum]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        have h1 : mono ε (c :: s) (k'⁻¹ * k) = coord ε c (k'⁻¹ * k) * mono ε s (k'⁻¹ * k) := by simp [mono]
        simp only [h1, coord_mul_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      · intro l _
        refine integrable_muK_of_continuous (continuous_const.mul ?_)
        exact ((continuous_mono ε s).comp (continuous_const.mul continuous_id)).mul
          ((continuous_coord ε _).mul hh)
    rw [e]
    refine Submodule.sum_mem _ fun l _ => ?_
    exact polyV_mono ε (show 1 + (d - 1) ≤ d by omega)
      (mul_mem (coord_inv_mem ε _) (ih (d - 1) (by omega) _ ((continuous_coord ε _).mul hh)))

theorem conv_mem {ε : Fin n → Bool} {d : ℕ} {e : KG ε → ℂ} (he : e ∈ polyV ε d) {h : KG ε → ℂ}
    (hh : Continuous h) : (fun k' : KG ε => ∫ k, e (k'⁻¹ * k) * h k ∂(muK ε)) ∈ polyV ε d := by
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact conv_mono_mem ε s d hs h hh
  | zero =>
    simpa using const_mem ε d 0
  | add x y hx hy ihx ihy =>
    convert add_mem ihx ihy using 1
    funext k'
    simp only [Pi.add_apply, add_mul]
    refine integral_add (integrable_muK_of_continuous ?_) (integrable_muK_of_continuous ?_)
    · exact ((continuous_of_mem (d := d) hx).comp (continuous_const.mul continuous_id)).mul hh
    · exact ((continuous_of_mem (d := d) hy).comp (continuous_const.mul continuous_id)).mul hh
  | smul a x _ ih =>
    convert Submodule.smul_mem _ a ih using 1
    funext k'
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

theorem avgK_mem : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i →
    ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε,
      GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  intro n ε i e he f hf y hy
  have hh : Continuous fun k : KG ε => f (y * toMK k) :=
    hf.comp_continuous (continuous_const.mul (GlobalTheory.TypeSum.continuous_toMK ε))
      fun k => GlobalTheory.TypeSum.mul_mem_UJ hy (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))
  convert conv_mem he hh using 1
  funext k'
  rw [← integral_mul_left_eq_self (μ := muK ε) _ k']
  simp only [avgK, inv_mul_cancel_left, toMK_mul, Matrix.mul_assoc]

end GlobalTheory.KFourier

end
