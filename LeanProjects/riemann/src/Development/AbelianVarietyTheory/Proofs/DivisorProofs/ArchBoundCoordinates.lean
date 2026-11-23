import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchAt
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay.Coord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embEquiv (w : InfinitePlace F) :
    letI : Algebra F ℂ := w.embedding.toAlgebra
    EmbOver E w ≃ (E →ₐ[F] ℂ) :=
  letI : Algebra F ℂ := w.embedding.toAlgebra
  { toFun := fun t => { t.1 with commutes' := fun x => RingHom.congr_fun t.2 x }
    invFun := fun s => ⟨s, RingHom.ext s.commutes⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

open Classical in
theorem embedding_trace (w : InfinitePlace F) (x : E) :
    w.embedding (Algebra.trace F E x) = ∑ τ : EmbOver E w, τ.1 x := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  have h := trace_eq_sum_embeddings (K := F) (L := E) ℂ (x := x)
  refine h.trans ?_
  exact (Fintype.sum_equiv (embEquiv w) _ _ fun _ => rfl).symm

theorem exists_repr_eq_trace (r : Fin (Module.finrank F E)) :
    ∃ c : E, ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x) := by
  classical
  refine ⟨(Module.finBasis F E).traceDual r, fun x => ?_⟩
  conv_rhs => rw [← (Module.finBasis F E).sum_repr x]
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, Module.Basis.trace_traceDual_mul]
  simp

theorem archAt_algebraMap (w : InfinitePlace F) (x : F) :
    archAt F w (algebraMap F (AF F) x) = w.embedding x := by
  change InfinitePlace.Completion.extensionEmbedding w (evInf F w (algebraMap F (AF F) x)) = _
  rw [AlgHom.commutes]
  exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

open Classical in
theorem archAt_repr (r : Fin (Module.finrank F E)) {c : E}
    (hc : ∀ x : E, (Module.finBasis F E).repr x r = Algebra.trace F E (c * x)) (w : InfinitePlace F) (y : AE F E) :
    archAt F w ((coB F E).repr y r) = ∑ τ : EmbOver E w, τ.1 c * piInf τ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]
  | tmul a x =>
    have h1 : (coB F E).repr (a ⊗ₜ[F] x) r = a * algebraMap F (AF F) ((Module.finBasis F E).repr x r) := by
      simp [coB, Algebra.TensorProduct.basis_repr_tmul]
    have h2 : ∀ τ : EmbOver E w, piInf τ (a ⊗ₜ[F] x) = archAt F w a * τ.1 x := fun τ => rfl
    rw [h1, map_mul, archAt_algebraMap, hc, embedding_trace, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [h2, map_mul]; ring

theorem coord_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : ℝ, 0 ≤ K ∧
    ∀ (y : AE F E) (B : ℝ), 0 ≤ B → (∀ (w : InfinitePlace F) (τ : EmbOver E w), ‖piInf τ y‖ ≤ B) →
    ∀ r w, ‖archAt F w ((coB F E).repr y r)‖ ≤ K * B := by
  classical
  intro F E _ _ _ _ _
  choose c hc using exists_repr_eq_trace (F := F) (E := E)
  let f : Fin (Module.finrank F E) × InfinitePlace F → ℝ := fun p => ∑ τ : EmbOver E p.2, ‖τ.1 (c p.1)‖
  have hf : ∀ p, 0 ≤ f p := fun p => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨∑ p, f p, Finset.sum_nonneg fun p _ => hf p, fun y B hB h r w => ?_⟩
  rw [archAt_repr r (hc r) w y]
  refine (norm_sum_le _ _).trans (le_trans ?_ (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := f) (fun p _ => hf p) (Finset.mem_univ (r, w))) hB))
  simp only [f]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h w τ) (norm_nonneg _)

end GlobalTheory.ThetaDecay.Coord

end
