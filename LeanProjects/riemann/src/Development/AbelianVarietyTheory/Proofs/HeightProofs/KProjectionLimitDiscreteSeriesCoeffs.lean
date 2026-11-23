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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactAverageKFiniteFiniteRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.KProjApprox

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero' : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) := ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add' {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', max (max C C') 0, words_append hS hS', fun w hw => ?_⟩
  have e1 := hC w hw
  have e2 := hC' w hw
  have s1 : 0 ≤ sobNorm σ S w := sobNorm_nonneg σ S w
  have s2 : 0 ≤ sobNorm σ S' w := sobNorm_nonneg σ S' w
  have h3 : sobNorm σ (S ++ S') w = sobNorm σ S w + sobNorm σ S' w := sobNorm_append σ S S' w
  change ‖ℓ w + ℓ' w‖ ≤ max (max C C') 0 * sobNorm σ (S ++ S') w
  change ‖ℓ w‖ ≤ C * sobNorm σ S w at e1
  change ‖ℓ' w‖ ≤ C' * sobNorm σ S' w at e2
  rw [h3]
  have a1 : C * sobNorm σ S w ≤ max (max C C') 0 * sobNorm σ S w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _)) s1
  have a2 : C' * sobNorm σ S' w ≤ max (max C C') 0 * sobNorm σ S' w :=
    mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _)) s2
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul' (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have e1 := hC w hw
  change ‖c * ℓ w‖ ≤ ‖c‖ * C * (S.map fun l => ‖l.foldr (dRep σ) w‖).sum
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left e1 (norm_nonneg c)

theorem sobCont_sum {ι : Type} (s : Finset ι) (ℓ : ι → (H →ₗ[ℂ] ℂ)) (h : ∀ i, Sobolev₂ (lieSet ε) σ (ℓ i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, ℓ i) :=
  Finset.sum_induction _ _ (fun _ _ => sobCont_add') sobCont_zero' fun i _ => h i

end GlobalTheory.TypeSum.KProjApprox

namespace GlobalTheory.TypeSum

open GlobalTheory.TypeSum.KProjApprox

theorem kAvg_approx_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
    ∃ (d : ℕ) (w : Fin d → H), (∀ a, IsKFin ε σ (w a)) ∧
      ∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
        ∃ L : Fin d → (H →ₗ[ℂ] ℂ), (∀ a, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (L a)) ∧
          ∀ y ∈ C, y ∈ UJset ε →
            ‖(∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) - ∑ a, L a (σ y (w a))‖ < δ := by
  intro n ε H _ _ _ σ h f hf happ e he hK
  obtain ⟨m, a, c, -, haK, -, hsum⟩ := kAvg_finite_rank n ε H σ h e hK
  refine ⟨m, a, haK, fun C hC δ hδ => ?_⟩
  have : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  set I := ∫ k, ‖e k‖ ∂(muK ε) with hIdef
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hC' : IsCompact ((fun p : Mx n × KG ε => p.1 * toMK p.2) '' (C ×ˢ Set.univ)) :=
    (hC.prod isCompact_univ).image (continuous_fst.mul ((continuous_toMK ε).comp continuous_snd))
  obtain ⟨m', ℓ, v, hℓ, hv, happ'⟩ := happ _ hC' (δ / (1 + I)) (by positivity)
  refine ⟨fun j => ∑ i, ⟪c j, v i⟫_ℂ • ℓ i, fun j => sobCont_sum _ _ fun i => sobCont_smul' _ (hℓ i),
    fun y hy hyU => ?_⟩
  have hsm : ∀ w, Sm ε σ (kAvg ε σ e w) := fun w => h.2.2.1 _ (by
    rw [hsum]
    exact (kfin ε σ).sum_mem fun j _ => (kfin ε σ).smul_mem _ (haK j))
  have hmem : ∀ k : KG ε, y * toMK k ∈ UJset ε := fun k => mul_mem_UJ hyU (GlobalTheory.ExpansionAverage.toMK_mem k)
  have hcm : Continuous fun k : KG ε => y * toMK k := continuous_const.mul (continuous_toMK ε)
  have hci : ∀ i, Continuous fun k : KG ε => ℓ i (σ (y * toMK k) (v i)) := fun i =>
    (h.continuousOn_coef (hℓ i) (hv i)).comp_continuous hcm hmem
  have hcf : Continuous fun k : KG ε => f (y * toMK k) := hf.comp_continuous hcm hmem
  have h1 : ∀ i, ℓ i (σ y (kAvg ε σ e (v i))) = ∫ k, e k * ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    intro i
    have := GlobalTheory.ExpansionAverage.form_kAvg h he (sobCont_translate h.1 (hℓ i) hyU) (hv i) (hsm _)
    simpa [sigma_mul h.1 hyU (GlobalTheory.ExpansionAverage.toMK_mem _)] using this
  have hid : ∑ j, (∑ i, ⟪c j, v i⟫_ℂ • ℓ i) (σ y (a j)) =
      ∫ k, e k * ∑ i, ℓ i (σ (y * toMK k) (v i)) ∂(muK ε) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum (f := fun i k => e k * ℓ i (σ (y * toMK k) (v i))) Finset.univ
      fun i _ => GlobalTheory.ExpansionAverage.integrable_K (he.mul (hci i))]
    simp_rw [← h1, hsum, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
  have hint : ∀ k : KG ε, ‖e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))‖ ≤ ‖e k‖ * (δ / (1 + I)) := by
    intro k
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (happ' _ ⟨(y, k), ⟨hy, Set.mem_univ _⟩, rfl⟩ (hmem k)).le (norm_nonneg _)
  have i1 : Integrable (fun k : KG ε => e k * f (y * toMK k)) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul hcf)
  have i2 : Integrable (fun k : KG ε => e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) (muK ε) :=
    GlobalTheory.ExpansionAverage.integrable_K (he.mul (continuous_finsetSum _ fun i _ => hci i))
  rw [hid, ← integral_sub i1 i2]
  calc ‖∫ k, (e k * f (y * toMK k) - e k * ∑ i, ℓ i (σ (y * toMK k) (v i))) ∂(muK ε)‖
      ≤ ∫ k, ‖e k‖ * (δ / (1 + I)) ∂(muK ε) :=
        norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (he.norm.mul continuous_const))
          (Filter.Eventually.of_forall hint)
    _ = I * (δ / (1 + I)) := integral_mul_const _ _
    _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
