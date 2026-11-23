import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DOpDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOrbitCoefficientSmooth

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open GlobalTheory.HeisOrbit GlobalTheory.HeisOrbitSmooth

noncomputable section

namespace GlobalTheory.HeisOrbitSmoothLeft

open scoped ContDiff

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

local notation "Vs" κ => (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)

theorem at_mul_left {x : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evI F) x) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    At (evI F) (A * x) := by
  intro a ha
  rw [← Matrix.mul_smul, hx a ha, Matrix.mul_zero]

theorem continuous_mat_line_left (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous fun t : ℝ => mat (γ (Multiplicative.ofAdd t)) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (hγ.comp continuous_ofAdd))

theorem mat_mul_left (g h : UA σ X.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one_left : mat (1 : UA σ X.J) = 1 := rfl

def opLl (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) : (Vs (Fin n × Fin d)) →ₗ[ℝ] Vs (Fin n × Fin d) where
  toFun w := GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w)
  map_add' w w' := by rw [lift_add, Matrix.mul_add, archCo_add]
  map_smul' c w := by rw [lift_smul, Matrix.mul_smul, archCo_smul]; rfl

theorem opLl_apply (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) (w) :
    opLl M g w = GlobalTheory.HeisOrbit.archCo M.co (g * lift M.co w) := rfl

theorem opLl_archCo (M : Model σ X W) (g : Matrix (Fin n) (Fin n) (AE F E)) {x : Matrix (Fin n) (Fin d) (AE F E)}
    (hx : At (evI F) x) : opLl M g (GlobalTheory.HeisOrbit.archCo M.co x) = GlobalTheory.HeisOrbit.archCo M.co (g * x) := by
  rw [opLl_apply, lift_archCo M.co hx]

def opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) :
    (Vs (Fin n × Fin d)) →L[ℝ] Vs (Fin n × Fin d) :=
  LinearMap.toContinuousLinearMap (opLl M (mat (γ (Multiplicative.ofAdd t))))

theorem opRl_apply (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (t : ℝ) (w) :
    opRl M γ t w = opLl M (mat (γ (Multiplicative.ofAdd t))) w := rfl

theorem opRl_zero (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) : opRl M γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [opRl_apply, opLl_apply, ofAdd_zero, map_one, mat_one_left, Matrix.one_mul, archCo_lift]
  rfl

theorem opRl_add (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (s t : ℝ) :
    opRl M γ (s + t) = opRl M γ s * opRl M γ t := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.mul_apply, opRl_apply, opRl_apply, opRl_apply,
    opLl_apply M (mat (γ (Multiplicative.ofAdd t))) w,
    opLl_archCo M _ (at_mul_left (at_lift M.co w) _),
    opLl_apply, ofAdd_add, map_mul, mat_mul_left, Matrix.mul_assoc]

theorem continuous_opRl (M : Model σ X W) (γ : Multiplicative ℝ →* UA σ X.J) (hγ : Continuous γ) :
    Continuous (opRl M γ) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  refine continuous_clm_apply.2 fun w => ?_
  simp only [opRl_apply, opLl_apply]
  exact (continuous_archCo M).comp ((continuous_mat_line_left γ hγ).matrix_mul continuous_const)

theorem archCo_orbit_smooth_left : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ X, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) ∧
    ∃ u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u' ∧
      HasDerivAt (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) (GlobalTheory.HeisOrbit.archCo M.co u') 0 := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ u hu
  haveI : CompleteSpace ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    FiniteDimensional.complete ℝ _
  haveI : FiniteDimensional ℝ (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    ContinuousLinearMap.finiteDimensional
  have hcomp : CompleteSpace (((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))
      →L[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F))) :=
    FiniteDimensional.complete ℝ _
  have hs : ContDiff ℝ ∞ (opRl M γ) :=
    @GlobalTheory.contDiff_of_continuous_oneParameter _ _ _ hcomp (opRl M γ) (continuous_opRl M γ hγ.1) (opRl_zero M γ)
      (opRl_add M γ)
  have hf : (fun t : ℝ => GlobalTheory.HeisOrbit.archCo M.co (mat (γ (Multiplicative.ofAdd t)) * u)) =
      fun t => opRl M γ t (GlobalTheory.HeisOrbit.archCo M.co u) := by
    funext t
    rw [opRl_apply, opLl_archCo M _ hu]
  rw [hf]
  refine ⟨hs.clm_apply contDiff_const, lift M.co (deriv (opRl M γ) 0 (GlobalTheory.HeisOrbit.archCo M.co u)), at_lift _ _, ?_⟩
  rw [archCo_lift]
  have hd : HasDerivAt (opRl M γ) (deriv (opRl M γ) 0) 0 :=
    ((hs.differentiable (by simp)) 0).hasDerivAt
  simpa using hd.clm_apply (hasDerivAt_const (0 : ℝ) (GlobalTheory.HeisOrbit.archCo M.co u))

end GlobalTheory.HeisOrbitSmoothLeft

end
