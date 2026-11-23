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
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory Matrix Formalism.REAL

variable {n : ℕ}

def polyAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {f | ∃ d, ⇑f ∈ polyV ε d}
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using mul_mem ha hb⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨max a b, by simpa using add_mem (polyV_mono ε (le_max_left a b) ha) (polyV_mono ε (le_max_right a b) hb)⟩
  algebraMap_mem' := by
    intro c
    refine ⟨0, ?_⟩
    convert const_mem ε 0 c using 1
    funext k; simp [Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro f ⟨a, ha⟩
    refine ⟨a, ?_⟩
    convert star_mem ha using 1
    funext k; rfl

theorem toMK_injective (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  have h1 : ((a : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = ((b : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := Units.ext h
  exact Subtype.ext (Subtype.ext h1)

theorem polyAlg_separatesPoints (ε : Fin n → Bool) : (polyAlg ε).SeparatesPoints := by
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy (toMK_injective ε h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hc
    push_neg at hc
    exact hne (Matrix.ext hc)
  refine ⟨_, ⟨⟨coord ε (i, j, true), continuous_coord ε _⟩, ⟨1, show coord ε (i, j, true) ∈ polyV ε 1 from coord_mem ε _⟩, rfl⟩, ?_⟩
  simpa [coord] using hij

theorem polyAlg_dense (ε : Fin n → Bool) : (polyAlg ε).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ (polyAlg_separatesPoints ε)

theorem integrable_cont (ε : Fin n → Bool) (F : C(KG ε, ℂ)) : Integrable F (muK ε) :=
  F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_integral_cont (ε : Fin n → Bool) :
    Continuous fun F : C(KG ε, ℂ) => ∫ k, F k ∂(muK ε) := by
  refine (LipschitzWith.of_dist_le_mul fun F G => ?_).continuous (K := 1)
  rw [dist_eq_norm, ← integral_sub (integrable_cont ε F) (integrable_cont ε G)]
  have h := norm_integral_le_of_norm_le_const (μ := muK ε) (C := ‖F - G‖)
    (Filter.Eventually.of_forall fun k => by
      simpa using ContinuousMap.norm_coe_le_norm (F - G) k)
  simpa [probReal_univ, dist_eq_norm] using h

theorem eq_zero_of_orth_poly : ∀ {n : ℕ} (ε : Fin n → Bool) (h : KG ε → ℂ), Continuous h → (∀ d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d, ∫ k, star (q k) * h k ∂(muK ε) = 0) → h = 0 := by
  intro n ε h hc horth
  let H : C(KG ε, ℂ) := ⟨h, hc⟩
  let Φ : C(KG ε, ℂ) → ℂ := fun F => ∫ k, star (F k) * h k ∂(muK ε)
  have hΦ : Continuous Φ := by
    have : Continuous fun F : C(KG ε, ℂ) => star F * H := (continuous_star).mul continuous_const
    exact (continuous_integral_cont ε).comp this
  have hclosed : IsClosed {F : C(KG ε, ℂ) | Φ F = 0} := isClosed_eq hΦ continuous_const
  have hsub : ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {F | Φ F = 0} := by
    rintro F ⟨d, hd⟩
    exact horth d _ hd
  have hcl : closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) = Set.univ := by
    have := polyAlg_dense ε
    rw [← StarSubalgebra.topologicalClosure_coe, this]
    rfl
  have hH : Φ H = 0 := by
    have : H ∈ closure ((polyAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by rw [hcl]; trivial
    exact hclosed.closure_subset_iff.mpr hsub this

  have hint : ∫ k, (Complex.normSq (h k) : ℂ) ∂(muK ε) = 0 := by
    have e : (fun k => (Complex.normSq (h k) : ℂ)) = fun k => star (h k) * h k := by
      funext k; rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [e]; exact hH
  have hint' : ∫ k, Complex.normSq (h k) ∂(muK ε) = 0 := by
    rw [integral_complex_ofReal] at hint
    exact_mod_cast hint
  have hnn : 0 ≤ᵐ[muK ε] fun k => Complex.normSq (h k) := Filter.Eventually.of_forall fun k => Complex.normSq_nonneg _
  have hcn : Continuous fun k => Complex.normSq (h k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hint'
  have hz : (fun k => Complex.normSq (h k)) = fun _ => 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hcn continuous_const).mp hae
  funext k
  have := congrFun hz k
  simpa using this

end GlobalTheory.KFourier

end
