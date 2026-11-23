import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairTransferAlongPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblLagrNondeg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR_rat (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem eq_zero_of_trace (e : E) (h : ∀ t : E, Algebra.trace F E (t * e) = 0) : e = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  by_contra he
  have h1 := h e⁻¹
  rw [inv_mul_cancel₀ he, ← map_one (algebraMap F E), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one,
    Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := F) (M := E)).ne' h1

theorem sum_vmv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E)
    (p r : α → E) (q s : β → E) :
    ∑ i, ∑ j, ∑ k, ∑ l, Matrix.vecMulVec p q i j * JA i k * JB j l * σ (Matrix.vecMulVec r s k l) =
      (p ⬝ᵥ JA *ᵥ fun k => σ (r k)) * (q ⬝ᵥ JB *ᵥ fun l => σ (s l)) := by
  have e1 : ∀ i j, (∑ k, ∑ l, Matrix.vecMulVec p q i j * JA i k * JB j l * σ (Matrix.vecMulVec r s k l)) =
      (∑ k, p i * (JA i k * σ (r k))) * (∑ l, q j * (JB j l * σ (s l))) := by
    intro i j
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.vecMulVec_apply, map_mul]
    ring
  simp_rw [e1]
  rw [← Finset.sum_mul_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

theorem hTens_vmv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E)
    (p r : α → E) (q s : β → E) :
    hTens (cA σ) (incM F JA) (incM F JB) (incM F (Matrix.vecMulVec p q)) (incM F (Matrix.vecMulVec r s)) =
      inclR (F := F) (AF F) ((p ⬝ᵥ JA *ᵥ fun k => σ (r k)) * (q ⬝ᵥ JB *ᵥ fun l => σ (s l))) := by
  rw [← sum_vmv σ]
  simp only [hTens, incM, Matrix.map_apply, GlobalTheory.MixXEvUniq.cA_inclR, ← map_mul, ← map_sum]

theorem symp_vmv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E) (JB : Matrix β β E)
    (p r : α → E) (q s : β → E) :
    symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB) (incM F (Matrix.vecMulVec p q))
        (incM F (Matrix.vecMulVec r s)) =
      -algebraMap F (AF F) (Algebra.trace F E
        ((p ⬝ᵥ JA *ᵥ fun k => σ (r k)) * (q ⬝ᵥ JB *ᵥ fun l => σ (s l)))) := by
  rw [symp, hTens_vmv, neg_one_mul, map_neg, trace_inclR_rat]

theorem dbl_incM' {d : ℕ} (J : Matrix (Fin d) (Fin d) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ d r' s' : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d)
    (M : Model σ X W) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ → W.IsSkew σ B r' s' →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J))) (Fin n × Fin d ⊕ Fin n × Fin d)), IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
    ∀ u : Fin d → E, (∀ z : Fin d → E,
      (dd.e (incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).1 ⬝ᵥ (dd.e (incM F (Matrix.vecMulVec H.x (Sum.elim z 0)))).2 =
        (dd.e (incM F (Matrix.vecMulVec H.x (Sum.elim z 0)))).1 ⬝ᵥ (dd.e (incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))).2) →
    u = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ d r' s' X X₁ W M H j₀ j₁ hH hW dd hdd u hu
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hval : ∀ (p r : Fin n → E) (q s : Fin d ⊕ Fin d → E),
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (incM F (Matrix.vecMulVec p q))
          (incM F (Matrix.vecMulVec r s)) =
        -algebraMap F (AF F) (Algebra.trace F E (form σ X.J p r * (q ⬝ᵥ dbl W.J *ᵥ fun l => σ (s l)))) := by
    intro p r q s
    rw [dbl_incM', symp_vmv, form]
  have hanti : ∀ a b, symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) a b =
      -symp (R := AF F) (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) b a := by
    intro a b
    rw [dd.form, dd.form]
    ring
  have hdiag : ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u) = Sum.elim u u := by
    simp [diagCols, Matrix.fromRows_mulVec]
  have hsum : ∀ z : Fin d → E, (Sum.elim u u ⬝ᵥ dbl W.J *ᵥ fun l => σ (Sum.elim z (0 : Fin d → E) l)) = form σ W.J u z := by
    intro z
    have e : (fun l => σ (Sum.elim z (0 : Fin d → E) l)) = Sum.elim (fun l => σ (z l)) (0 : Fin d → E) := by
      funext l
      cases l <;> simp
    rw [e]
    simp [form, dbl, Matrix.fromBlocks_mulVec]
  have htr : ∀ z : Fin d → E, Algebra.trace F E (form σ X.J H.y H.x * form σ W.J u z) = 0 := by
    intro z
    have h1 := dd.form (incM F (Matrix.vecMulVec H.y ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) E) *ᵥ u)))
      (incM F (Matrix.vecMulVec H.x (Sum.elim z 0)))
    rw [hu z, sub_self, hval, hdiag, hsum, neg_eq_zero] at h1
    exact GlobalTheory.MixXEvUniq.alg_inj (h1.trans (map_zero _).symm)
  have hf : ∀ z, form σ W.J u z = 0 := by
    by_cases hc0 : form σ X.J H.y H.x = 0
    · have key : ∀ q s : Fin d ⊕ Fin d → E, Algebra.trace F E (q ⬝ᵥ dbl W.J *ᵥ fun l => σ (s l)) = 0 := by
        intro q s
        have h1 := hanti (incM F (Matrix.vecMulVec H.x q)) (incM F (Matrix.vecMulVec H.y s))
        rw [hval, hval, hH.xy, hc0, one_mul, zero_mul, map_zero, map_zero, neg_zero, neg_zero, neg_eq_zero] at h1
        exact GlobalTheory.MixXEvUniq.alg_inj (h1.trans (map_zero _).symm)
      intro z
      rw [← hsum]
      refine eq_zero_of_trace (F := F) _ fun t => ?_
      have h2 := key (t • Sum.elim u u) (Sum.elim z 0)
      rwa [smul_dotProduct, smul_eq_mul] at h2
    · intro z
      have hσ : Function.Surjective σ := (AlgHom.bijective σ).2
      have h3 : form σ X.J H.y H.x * form σ W.J u z = 0 := by
        refine eq_zero_of_trace (F := F) _ fun t => ?_
        obtain ⟨t', rfl⟩ := hσ t
        have h2 := htr (t' • z)
        have e : form σ W.J u (t' • z) = σ t' * form σ W.J u z := by
          simp only [form, Pi.smul_apply, smul_eq_mul, map_mul]
          rw [show (fun i => σ t' * σ (z i)) = σ t' • fun i => σ (z i) from rfl, Matrix.mulVec_smul,
            dotProduct_smul, smul_eq_mul]
        rw [e, mul_left_comm] at h2
        exact h2
      exact (mul_eq_zero.mp h3).resolve_left hc0
  have hv : u ᵥ* W.J = 0 := by
    funext l
    have h1 := hf (Pi.single l 1)
    have hs : (fun i => σ ((Pi.single l (1 : E) : Fin d → E) i)) = (Pi.single l (1 : E) : Fin d → E) := by
      funext i
      by_cases h : i = l
      · subst h; simp
      · simp [Pi.single_apply, h]
    simp only [form] at h1
    rw [hs, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h1
    exact h1
  exact Matrix.eq_zero_of_vecMul_eq_zero (GlobalTheory.LeviAdapted.det_ne_zero hW) hv

end GlobalTheory.DblLagrNondeg
