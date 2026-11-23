import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchDualPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR' (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem hTens_vecMulVec' (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (x x' : Fin n → E) (y y' : Fin d → E) :
    hTens σ JA JB (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = form σ JA x x' * form σ JB y y' := by
  unfold hTens form
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_incM (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (A B : Matrix (Fin n) (Fin d) E) :
    hTens (cA σ) (incM F JA) (incM F JB) (incM F A) (incM F B) = inclR (F := F) (AF F) (hTens σ JA JB A B) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  simp only [hTens, incM, Matrix.map_apply, hc, map_mul, map_sum]

theorem lhs_eq {n d : ℕ} (b : E) (x : Fin n → E) (y' : Fin d → E) :
    inclR (F := F) (AF F) b • Matrix.vecMulVec (incV F x) (incV F y') = incM F (Matrix.vecMulVec (b • x) y') := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply, mul_assoc]

theorem rhs_eq {n d : ℕ} (t : E) (y : Fin n → E) (x' : Fin d → E) :
    Matrix.vecMulVec (inclR (F := F) (AF F) t • incV F y) (incV F x') = incM F (Matrix.vecMulVec (t • y) x') := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply, mul_assoc]

theorem form_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (b t : E) (x y : Fin n → E) :
    form σ J (b • x) (t • y) = b * σ t * form σ J x y := by
  simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ t * σ (y i)) = σ t • fun i => σ (y i) from rfl, Matrix.mulVec_smul, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

end GlobalTheory.ArchDualPair

theorem GlobalTheory.ArchDualPair.dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Fin n → E) (x' y' : Fin d → E),
    form σ J x y = 1 → form σ J' y' x' = -1 → ∃ t : Fin (Module.finrank F E) → E, ∀ i j,
      symp (R := AF F) (cA σ) (-1) (incM F J) (incM F J')
        (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F x) (incV F y'))
        (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F y) (incV F x')) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ σ n d J J' x y x' y' h1 h2
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bb := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) bb
  have hbij : Function.Bijective σ := σ.bijective
  let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hbij
  refine ⟨fun i => s.symm (b' i), fun i j => ?_⟩
  have hσt : σ (s.symm (b' i)) = b' i := s.apply_symm_apply (b' i)
  rw [GlobalTheory.ArchDualPair.lhs_eq, GlobalTheory.ArchDualPair.rhs_eq, symp, GlobalTheory.ArchDualPair.hTens_incM,
    GlobalTheory.ArchDualPair.hTens_vecMulVec', GlobalTheory.ArchDualPair.form_smul, hσt, h1, h2,
    show (-1 : AE F E) = inclR (F := F) (AF F) (-1) by simp, ← map_mul, GlobalTheory.ArchDualPair.trace_inclR']
  have ht : Algebra.trace F E (-1 * (bb j * b' i * 1 * -1)) = Algebra.traceForm F E (b' i) (bb j) := by
    rw [Algebra.traceForm_apply]; congr 1; ring
  rw [ht, LinearMap.BilinForm.apply_dualBasis_left]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
