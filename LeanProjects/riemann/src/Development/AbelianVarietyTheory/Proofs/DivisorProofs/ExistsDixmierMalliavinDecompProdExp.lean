import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DixmierMalliavinFactorisationBasisStepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctional
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem integrable_integral_fin_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {F : (Fin (n + 1) → ℝ) → E} (hF : Integrable F) :
    Integrable (fun s : ℝ => ∫ t', F (Fin.cons s t')) := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  refine hint.integral_prod_left.congr (ae_of_all _ fun s => ?_)
  simp only
  congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]
  rfl

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem prodExp_fin_succ (h : IsExpLieAlgebra G 𝔤) {n : ℕ} (X : Fin (n + 1) → 𝔤) (t : Fin (n + 1) → ℝ) :
    h.prodExp X t = h.expG (t 0 • X 0) * h.prodExp (Fin.tail X) (Fin.tail t) := by
  simp [IsExpLieAlgebra.prodExp, List.ofFn_succ, Fin.tail]

theorem integral_mul_sum_cons_kernel (h : IsExpLieAlgebra G 𝔤) {n N : ℕ} (X : Fin (n + 1) → 𝔤) {ε : ℝ}
    (hε : 0 ≤ ε) {u : ℝ → ℂ} (hu : Continuous u) (hus : tsupport u ⊆ Set.Icc (-ε) ε)
    {κ : Fin N → (Fin n → ℝ) → ℂ} (hκ : ∀ m, Continuous (κ m))
    (hκs : ∀ m, tsupport (κ m) ⊆ Metric.closedBall 0 ε) {Φ : Fin N → G → ℂ}
    (hΦ : ∀ m, Continuous (Φ m)) (Ψ : ℝ → ℂ)
    (hΨ : ∀ s, Ψ s = ∑ m, ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t')) :
    ∫ s, u s * Ψ s = ∑ m, ∫ t, u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t) := by
  have hF : ∀ m, Integrable (fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t) * Φ m (h.prodExp X t)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.comp (continuous_apply 0)).mul
        ((hκ m).comp (continuous_pi fun j => continuous_apply j.succ))).mul
        ((hΦ m).comp (h.continuous_prodExp X))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (n + 1) → ℝ => u (t 0) * κ m (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε hus (hκs m)))
  have heq : ∀ m s, u s * ∫ t', κ m t' * Φ m (h.expG (s • X 0) * h.prodExp (Fin.tail X) t') =
      ∫ t', u ((Fin.cons s t' : Fin (n + 1) → ℝ) 0) * κ m (Fin.tail (Fin.cons s t' : Fin (n + 1) → ℝ)) *
        Φ m (h.prodExp X (Fin.cons s t')) := by
    intro m s
    rw [← integral_const_mul]
    congr 1; funext t'
    simp only [Fin.cons_zero, Fin.tail_cons, prodExp_fin_succ h X, mul_assoc]
  simp_rw [hΨ, Finset.mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    simp_rw [heq m]; exact integrable_integral_fin_cons (hF m))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [heq m]
  exact (integral_fin_succ_cons (hF m)).symm

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem SmFn.exists_decomp_prodExp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (j : Fin n → Fin d) (Λ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ → ∃ (N : ℕ) (Λ' : Fin N → List (Fin d) → (G → ℂ) → ℂ) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ m, SmFn h b μ S K (Λ' m) ∧ ContDiff ℝ ∞ (κ m) ∧ tsupport (κ m) ⊆ Metric.closedBall 0 ε) ∧ ∀ f ∈ S, Λ [] f = ∑ m, ∫ t, κ m t * Λ' m [] fun y => f (h.prodExp (fun k => b (j k)) t * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK ε hε n
  induction n with
  | zero =>
    intro j Λ hΛ
    refine ⟨1, fun _ => Λ, fun _ _ => 1, fun _ => ⟨hΛ, contDiff_const, ?_⟩, fun f hf => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      have hP : ∀ t : Fin 0 → ℝ, h.prodExp (fun k => b (j k)) t = 1 := fun t => by
        simp [IsExpLieAlgebra.prodExp]
      simp [hP, hv]
  | succ n ih =>
    intro j Λ hΛ
    obtain ⟨Λ', u, v, hΛ', hu, hv, hus, hvs, hdec⟩ :=
      GlobalTheory.T.dixmierMalliavin_factorisation_basis_step 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ hΛ (j 0) ε hε
    obtain ⟨N₁, Λ₁, κ₁, h₁, hd₁⟩ := ih (Fin.tail j) Λ' hΛ'
    obtain ⟨N₂, Λ₂, κ₂, h₂, hd₂⟩ := ih (Fin.tail j) Λ hΛ
    refine ⟨N₁ + N₂, Fin.append Λ₁ Λ₂,
      Fin.append (fun m t => u (t 0) * κ₁ m (Fin.tail t)) (fun m t => v (t 0) * κ₂ m (Fin.tail t)),
      ?_, ?_⟩
    · intro m
      refine Fin.addCases (fun m => ?_) (fun m => ?_) m
      · simp only [Fin.append_left]
        exact ⟨(h₁ m).1, contDiff_cons_kernel hu (h₁ m).2.1, tsupport_cons_kernel hε.le hus (h₁ m).2.2⟩
      · simp only [Fin.append_right]
        exact ⟨(h₂ m).1, contDiff_cons_kernel hv (h₂ m).2.1, tsupport_cons_kernel hε.le hvs (h₂ m).2.2⟩
    · intro f hf
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec f hf]
      have hc : ∀ (Λ₀ : List (Fin d) → (G → ℂ) → ℂ), SmFn h b μ S K Λ₀ →
          Continuous fun x : G => Λ₀ [] fun y => f (x * y) := fun Λ₀ hΛ₀ =>
        SmFn.continuous_leftTranslate 𝔸 G 𝔤 h d b μ hμ S hS hL K hK Λ₀ hΛ₀ [] f hf
      congr 1
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hu.continuous hus
          (fun m => (h₁ m).2.1.continuous) (fun m => (h₁ m).2.2)
          (Φ := fun m x => Λ₁ m [] fun y => f (x * y)) (fun m => hc _ (h₁ m).1) _
          (fun s => by
            rw [hd₁ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)
      · exact integral_mul_sum_cons_kernel h (fun k => b (j k)) hε.le hv.continuous hvs
          (fun m => (h₂ m).2.1.continuous) (fun m => (h₂ m).2.2)
          (Φ := fun m x => Λ₂ m [] fun y => f (x * y)) (fun m => hc _ (h₂ m).1) _
          (fun s => by
            rw [hd₂ _ (hL f hf _)]
            simp only [mul_assoc]
            rfl)

end GlobalTheory.HCA
