import Mathlib
import Formalism.PeriodIntegrals.IsoDualPair

noncomputable section

open scoped ComplexConjugate

namespace PI.IsoDualPair.UnitaryGroupMassFormula

open PI.IsoDualPair

instance finite_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Finite (ColChoice N nu) := by
  unfold ColChoice
  have : ∀ a, Finite (Fin a ↪o Fin N) := fun a =>
    Finite.of_injective (fun e : Fin a ↪o Fin N => (e : Fin a → Fin N))
      (fun e f h => DFunLike.coe_injective h)
  infer_instance

noncomputable instance fintype_colChoice {Lt : Type} [Finite Lt] (N : ℕ) (nu : Lt → YoungDiagram) :
    Fintype (ColChoice N nu) := Fintype.ofFinite _

variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}

lemma prC_eq (φ ψ : LaC N nu) : prC φ ψ = ∑ J, φ J * ψ J := finsum_eq_sum_of_fintype _

lemma symmetricMeasure_l2Norm_eq_resolutionL2 (φ : LaC N nu) : l2 φ = ∑ J, ‖φ J‖ ^ 2 := finsum_eq_sum_of_fintype _

lemma cs (φ ψ : LaC N nu) : ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ := by
  rw [prC_eq, symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2]
  calc ‖∑ J, φ J * ψ J‖ ^ 2 ≤ (∑ J, ‖φ J‖ * ‖ψ J‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun J _ => norm_mul_le _ _)
    _ ≤ (∑ J, ‖φ J‖ ^ 2) * ∑ J, ‖ψ J‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma hvC_conj (x : Lt → Fin N → ℕ → ℂ) :
    (fun J => conj (hvC N nu x J)) = hvC N nu (fun s a j => conj (x s a j)) := by
  funext J
  simp only [hvC, minY, map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  rfl

lemma conj_mem {φ : LaC N nu} (h : φ ∈ Vnu N nu) : (fun J => conj (φ J)) ∈ Vnu N nu := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hvC_conj]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero =>
    have : (fun J => conj ((0 : LaC N nu) J)) = 0 := by funext J; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (fun J => conj ((x + y) J)) = (fun J => conj (x J)) + (fun J => conj (y J)) := by
      funext J; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (fun J => conj ((a • x) J)) = conj a • (fun J => conj (x J)) := by
      funext J; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

lemma prC_conj (φ : LaC N nu) : prC φ (fun J => conj (φ J)) = (l2 φ : ℂ) := by
  rw [prC_eq, symmetricMeasure_l2Norm_eq_resolutionL2, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma l2_conj (φ : LaC N nu) : l2 (fun J => conj (φ J)) = l2 φ := by
  rw [symmetricMeasure_l2Norm_eq_resolutionL2, symmetricMeasure_l2Norm_eq_resolutionL2]
  simp

lemma eq_zero_of_l2_eq_zero (φ : LaC N nu) (h : l2 φ = 0) : φ = 0 := by
  rw [symmetricMeasure_l2Norm_eq_resolutionL2] at h
  funext J
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => by positivity)).1 h J (Finset.mem_univ _)
  simpa using this

def pairL : Vnu N nu →ₗ[ℂ] Module.Dual ℂ (Vnu N nu) :=
  LinearMap.mk₂ ℂ (fun φ ψ : Vnu N nu => prC (φ : LaC N nu) ψ)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun a b c => by
      simp only [Submodule.coe_add, prC_eq, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun J _ => by ring)
    (fun r a b => by
      simp only [Submodule.coe_smul, prC_eq, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring)

lemma pairL_apply (φ ψ : Vnu N nu) : pairL φ ψ = prC (φ : LaC N nu) ψ := rfl

lemma pairL_injective : Function.Injective (pairL (N := N) (nu := nu)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have h1 := LinearMap.congr_fun hφ ⟨_, conj_mem φ.2⟩
  rw [pairL_apply, LinearMap.zero_apply] at h1
  have h2 : prC (φ : LaC N nu) (fun J => conj ((φ : LaC N nu) J)) = 0 := h1
  rw [prC_conj] at h2
  have h3 : l2 (φ : LaC N nu) = 0 := by exact_mod_cast h2
  exact Subtype.ext (eq_zero_of_l2_eq_zero _ h3)

lemma pairL_surjective : Function.Surjective (pairL (N := N) (nu := nu)) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 pairL_injective

theorem isoDualPair : IsoDualPair := by
  intro Lt _ _ N nu
  refine ⟨fun φ hφ => ⟨fun ψ _ => cs φ ψ, ⟨_, conj_mem hφ, l2_conj φ, prC_conj φ⟩⟩, fun Λ => ?_⟩
  obtain ⟨φ, hφ⟩ := pairL_surjective Λ
  refine ⟨φ, φ.2, fun ψ => ?_⟩
  rw [← hφ]
  rfl

end PI.IsoDualPair.UnitaryGroupMassFormula
