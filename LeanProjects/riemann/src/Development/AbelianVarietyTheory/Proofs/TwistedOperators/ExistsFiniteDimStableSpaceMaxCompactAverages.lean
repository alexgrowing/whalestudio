import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFinAvgSpan

open Formalism.REAL MeasureTheory GlobalTheory.SeriesToClosure Matrix
open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom

theorem continuous_integral_K {n : ℕ} {ε : Fin n → Bool} {X : Type*} [TopologicalSpace X] (F : X → KG ε → ℂ)
    (hF : Continuous (Function.uncurry F)) : Continuous fun x => ∫ k, F x k ∂(muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ k, g k ∂(muK ε)
      map_add' := fun g h => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (GlobalTheory.ExpansionAverage.integrable_K g.continuous)
          (GlobalTheory.ExpansionAverage.integrable_K h.continuous)
      map_smul' := fun c g => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }
  have hL : Continuous L := AddMonoidHomClass.continuous_of_bound L ((muK ε).real Set.univ) fun g => by
    show ‖∫ k, g k ∂(muK ε)‖ ≤ _
    exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      ContinuousMap.norm_coe_le_norm g k)).trans (le_of_eq (mul_comm _ _))
  exact hL.comp (ContinuousMap.curry ⟨_, hF⟩).continuous

variable {D : D7} {θ : InfFam D} {V : HSp D} {τ : D.what₂.Tau} {ε : Fin V.rank → Bool}
  {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}

theorem continuous_conjAt (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ) :
    Continuous fun k : KG ε => atTau θ V τ (P⁻¹ * toMK k * P) :=
  (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
    fun k => conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))

theorem continuous_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    Continuous (Function.uncurry fun (x : GA D V) (k : KG ε) => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) :=
  (he.comp continuous_snd).mul (hφ.comp (continuous_fst.mul ((continuous_conjAt hθ hP hJ).comp continuous_snd)))

theorem integrable_integrand (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) (x : GA D V) :
    Integrable (fun k => e k * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) (muK ε) :=
  GlobalTheory.ExpansionAverage.integrable_K (he.mul (hφ.comp (continuous_const.mul (continuous_conjAt hθ hP hJ))))

theorem continuous_avg (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ : GA D V → ℂ} (hφ : Continuous φ) : Continuous (avg θ V τ ε P e φ) :=
  continuous_integral_K _ (continuous_integrand hθ hP hJ he hφ)

theorem avg_add_left (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e₁ e₂ : KG ε → ℂ} (h₁ : Continuous e₁) (h₂ : Continuous e₂) {φ : GA D V → ℂ} (hφ : Continuous φ) :
    avg θ V τ ε P (e₁ + e₂) φ = avg θ V τ ε P e₁ φ + avg θ V τ ε P e₂ φ := funext fun x => by
  simp only [avg, Pi.add_apply, add_mul]
  exact integral_add (integrable_integrand hθ hP hJ h₁ hφ x) (integrable_integrand hθ hP hJ h₂ hφ x)

theorem avg_smul_left (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P (c • e) φ = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem avg_add_right (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {e : KG ε → ℂ} (he : Continuous e) {φ₁ φ₂ : GA D V → ℂ} (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) :
    avg θ V τ ε P e (φ₁ + φ₂) = avg θ V τ ε P e φ₁ + avg θ V τ ε P e φ₂ := funext fun x => by
  simp only [avg, Pi.add_apply, mul_add]
  exact integral_add (integrable_integrand hθ hP hJ he h₁ x) (integrable_integrand hθ hP hJ he h₂ x)

theorem avg_smul_right (c : ℂ) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    avg θ V τ ε P e (c • φ) = c • avg θ V τ ε P e φ := funext fun x => by
  simp only [avg, Pi.smul_apply, smul_eq_mul, mul_left_comm (e _) c]
  exact integral_const_mul c _

theorem rTr_avg_same (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : P * g * P⁻¹ ∈ Kset ε) :
    ∃ k₀ : KG ε, ∀ (e : KG ε → ℂ) (φ : GA D V → ℂ),
      rTr V (atTau θ V τ g) (avg θ V τ ε P e φ) = avg θ V τ ε P (fun k => e (k₀⁻¹ * k)) φ := by
  obtain ⟨k₀, hk₀'⟩ : P * g * P⁻¹ ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hg
  have hk₀ : toMK k₀ = P * g * P⁻¹ := hk₀'
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have eg : g = P⁻¹ * toMK k₀ * P := by
    rw [hk₀]
    calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [Matrix.nonsing_inv_mul _ hd, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨k₀, fun e φ => funext fun x => ?_⟩
  have key : ∀ k : KG ε, atTau θ V τ g * atTau θ V τ (P⁻¹ * toMK k * P) =
      atTau θ V τ (P⁻¹ * toMK (k₀ * k) * P) := fun k => by
    rw [eg, ← at_mul hθ hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k₀)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))]
    rfl
  simp only [rTr, avg, mul_assoc x, key]
  rw [← integral_mul_left_eq_self (μ := muK ε)
    (fun k => e (k₀⁻¹ * k) * φ (x * atTau θ V τ (P⁻¹ * toMK k * P))) k₀]
  simp only [inv_mul_cancel_left]

theorem rTr_avg_other (hθ : IsInfFam θ) (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = gramAt D V τ)
    {τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ')) (e : KG ε → ℂ) (φ : GA D V → ℂ) :
    rTr V (atTau θ V τ' g) (avg θ V τ ε P e φ) = avg θ V τ ε P e (rTr V (atTau θ V τ' g) φ) := funext fun x => by
  simp only [rTr, avg, mul_assoc x]
  congr 1
  funext k
  rw [GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' hne _
    (conj_inv_mem hP hJ (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k))) g hg]

end GlobalTheory.KFinAvgSpan

namespace GlobalTheory.KFinAvgSpan

set_option maxHeartbeats 1600000 in

theorem exists_stab_insert : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  intro D θ hθ N τ e he s hτs W' hW'fin hW'c hW'stab
  obtain ⟨F, hFfin, heF, hFc, hFtr⟩ := he
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI := hFfin
  haveI := hW'fin
  let B : F →ₗ[ℂ] W' →ₗ[ℂ] (GA D N.V → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ)
        (b : GA D N.V → ℂ))
      (fun a₁ a₂ b => avg_add_left hθ hP hJ (hFc _ a₁.2) (hFc _ a₂.2) (hW'c _ b.2))
      (fun c a b => avg_smul_left c _ _)
      (fun a b₁ b₂ => avg_add_right hθ hP hJ (hFc _ a.2) (hW'c _ b₁.2) (hW'c _ b₂.2))
      (fun c a b => avg_smul_right c _ _)
  have hB : ∀ (a : F) (b : W'), TensorProduct.lift B (a ⊗ₜ b) =
      GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ) :=
    fun a b => by rw [TensorProduct.lift.tmul]; rfl
  have hcont : ∀ t, Continuous (TensorProduct.lift B t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact continuous_const
    | tmul a b => rw [hB]; exact continuous_avg hθ hP hJ (hFc _ a.2) (hW'c _ b.2)
    | add u v hu hv => rw [map_add]; exact hu.add hv
  refine ⟨LinearMap.range (TensorProduct.lift B), inferInstance, ?_, ?_, fun f hf => ⟨⟨e, heF⟩ ⊗ₜ ⟨f, hf⟩, hB _ _⟩⟩
  · rintro _ ⟨t, rfl⟩
    exact hcont t
  · intro τ'' hτ'' g hg hK w hw
    obtain ⟨t, rfl⟩ := hw
    suffices h : ∀ (a : F) (b : W'), rTr N.V (atTau θ N.V τ'' g)
        (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)) ∈
          LinearMap.range (TensorProduct.lift B) by
      induction t using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        exact zero_mem _
      | tmul a b => rw [hB]; exact h a b
      | add u v hu hv =>
        rw [map_add]
        exact add_mem hu hv
    intro a b
    rcases hτ'' with h | hs
    · rw [h] at hK ⊢
      obtain ⟨k₀, hk⟩ := rTr_avg_same hθ hP hJ hK
      have hk' := hk (a : Formalism.REAL.KG (N.M.ε τ) → ℂ) (b : GA D N.V → ℂ)
      refine ⟨⟨_, (hFtr _ a.2 k₀⁻¹).1⟩ ⊗ₜ b, ?_⟩
      rw [hB, hk']
    · have hne : τ ≠ τ'' := fun h => hτs (h ▸ hs)
      rw [rTr_avg_other hθ hP hJ hne hg]
      exact ⟨a ⊗ₜ ⟨_, hW'stab τ'' hs g hg hK b b.2⟩, hB _ _⟩

end GlobalTheory.KFinAvgSpan

end
