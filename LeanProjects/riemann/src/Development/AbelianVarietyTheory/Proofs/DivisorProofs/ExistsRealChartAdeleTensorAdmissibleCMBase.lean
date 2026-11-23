import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB

noncomputable section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF.CMChart

open Formalism.L2.Fam.ThC

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rc [IsTotallyReal F] (v : InfinitePlace F) : v.Completion ≃+* ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)

theorem compF_eq [IsTotallyReal F] (τ : E →+* ℂ) (w : InfinitePlace F) (h : plF (F := F) τ = w) (a : Ainf F) :
    compF (F := F) τ a = (rc w (a w) : ℝ) := by
  subst h
  exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal _) _).symm

def rho [IsTotallyReal F] : (InfinitePlace F → ℝ) →+ Ainf F where
  toFun x v := (rc v).symm (x v)
  map_zero' := funext fun v => map_zero (rc v).symm
  map_add' _ _ := funext fun v => map_add (rc v).symm _ _

theorem continuous_rho [IsTotallyReal F] : Continuous (rho (F := F)) :=
  continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.continuous.comp
      (continuous_apply v)

theorem rc_rho [IsTotallyReal F] (x : InfinitePlace F → ℝ) (w : InfinitePlace F) : rc w (rho x w) = x w :=
  (rc w).apply_symm_apply _

def embA (e : E) : Ainf F →+ AEF F E where
  toFun a := pairA F a 0 ⊗ₜ[F] e
  map_zero' := TensorProduct.zero_tmul _ _
  map_add' a b := by
    rw [← TensorProduct.add_tmul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm

theorem continuous_embA (e : E) : Continuous (embA (F := F) e) := by
  haveI := isModuleTopology_AE F E
  have h1 : Continuous fun a : Ainf F => pairA F a 0 :=
    Continuous.prodMk continuous_id continuous_const
  have h2 : Continuous fun a : AF F => a • ((1 : AF F) ⊗ₜ[F] e : AEF F E) :=
    continuous_smul.comp (continuous_id.prodMk continuous_const)
  refine (h2.comp h1).congr fun a => ?_
  show pairA F a 0 • ((1 : AF F) ⊗ₜ[F] e : AEF F E) = pairA F a 0 ⊗ₜ[F] e
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem finPart_embA (e : E) (a : Ainf F) : finPartF F E (embA e a) = 0 :=
  TensorProduct.zero_tmul _ e

theorem infPart_embA (e : E) (a : Ainf F) : infPartF F E (embA e a) = a ⊗ₜ[F] e := rfl

theorem tensor_span {M : Type} [AddCommGroup M] [Module F M] (δ : E)
    (h : ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x) (a : M ⊗[F] E) :
    ∃ a₀ a₁ : M, a = a₀ ⊗ₜ[F] (1 : E) + a₁ ⊗ₜ[F] δ := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul m x =>
    obtain ⟨u, v, rfl⟩ := h x
    exact ⟨u • m, v • m, by simp only [TensorProduct.tmul_add, TensorProduct.smul_tmul]⟩
  | add a b ha hb =>
    obtain ⟨a₀, a₁, rfl⟩ := ha
    obtain ⟨b₀, b₁, rfl⟩ := hb
    exact ⟨a₀ + b₀, a₁ + b₁, by simp only [TensorProduct.add_tmul]; abel⟩

theorem exists_gen {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ δ : E, (∀ τ : E →+* ℂ, (τ δ).im ≠ 0) ∧ ∀ x : E, ∃ u v : F, u • (1 : E) + v • δ = x := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hn : ¬ ComplexEmbedding.IsReal τ₀ := IsTotallyComplex.complexEmbedding_not_isReal τ₀
  have : ∃ δ : E, σ δ ≠ δ := by
    by_contra hcon
    push Not at hcon
    apply hn
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hσ τ₀ x
    rw [hcon] at this
    exact this.symm
  obtain ⟨δ, hδ⟩ := this
  refine ⟨δ, fun τ hτ => hδ (τ.injective ?_), ?_⟩
  · rw [hσ]
    exact Complex.conj_eq_iff_im.2 hτ
  · have hli : LinearIndependent F ![(1 : E), δ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h3 := congrArg σ hst
      rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, σ.commutes, σ.commutes, map_one, map_zero,
        ← Algebra.smul_def, ← Algebra.smul_def] at h3
      have h4 : t • (σ δ - δ) = 0 := by
        rw [smul_sub, eq_neg_of_add_eq_zero_right h3, eq_neg_of_add_eq_zero_right hst, sub_self]
      have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hδ)
      rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right one_ne_zero, ht⟩
    have hsp := hli.span_eq_top_of_card_eq_finrank (by rw [h2]; rfl)
    intro x
    have hx : x ∈ Submodule.span F (Set.range ![(1 : E), δ]) := hsp ▸ Submodule.mem_top
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union,
      Submodule.mem_span_pair] at hx
    exact hx

def fstC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).re - (z i).im / (c i).im * (c i).re
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_re, Complex.add_im]; ring

def sndC {I : Type} (c : I → ℂ) : (I → ℂ) →+ (I → ℝ) where
  toFun z i := (z i).im / (c i).im
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp only [Pi.add_apply, Complex.add_im]; ring

theorem exists_chart_of_cm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (tau : InfinitePlace F → (E →+* ℂ))
    (htau : ∀ w, plF (F := F) (tau w) = w) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (hθ : IsInfFamF tau θ) :
    ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  haveI : IsTotallyReal F := h.1
  obtain ⟨δ, hδ, hsp⟩ := exists_gen h
  have hθ' : ∀ w (a : Ainf F) (x : E), θ w (a ⊗ₜ[F] x) = (rc w (a w) : ℝ) * tau w x := by
    intro w a x
    rw [isInfEmb_unique (tau w) (hθ w) (projAt_isInfEmb (tau w)), projAt_tmul, compF_eq _ w (htau w)]
  let c : InfinitePlace F → ℂ := fun w => tau w δ
  let ι : (InfinitePlace F → ℂ) →+ AEF F E :=
    (embA 1).comp (rho.comp (fstC c)) + (embA δ).comp (rho.comp (sndC c))
  have hι : ∀ z, ι z = embA 1 (rho (fstC c z)) + embA δ (rho (sndC c z)) := fun _ => rfl
  refine ⟨ι, ?_, fun z => ?_, fun z w => ?_, fun a hf hi => ?_⟩
  · have c2 : ∀ w, Continuous fun z : InfinitePlace F → ℂ => (z w).im / (c w).im := fun w =>
      (Complex.continuous_im.comp (continuous_apply w)).div_const _
    have c1 : Continuous (fstC c) :=
      continuous_pi fun w => (Complex.continuous_re.comp (continuous_apply w)).sub ((c2 w).mul continuous_const)
    have c3 : Continuous (sndC c) := continuous_pi c2
    exact ((continuous_embA _).comp (continuous_rho.comp c1)).add ((continuous_embA _).comp (continuous_rho.comp c3))
  · rw [hι, RingHom.map_add, finPart_embA, finPart_embA, add_zero]
  · rw [hι, RingHom.map_add, infPart_embA, infPart_embA, RingHom.map_add, hθ', hθ', rc_rho, rc_rho, map_one, mul_one]
    have h0 : (c w).im ≠ 0 := hδ _
    show (((z w).re - (z w).im / (c w).im * (c w).re : ℝ) : ℂ) + (((z w).im / (c w).im : ℝ) : ℂ) * c w = z w
    apply Complex.ext
    · rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]; ring
    · rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, div_mul_cancel₀ _ h0]
  · obtain ⟨b₀, b₁, hb⟩ := tensor_span δ hsp (infPartF F E a)
    have key : ∀ w, rc w (b₀ w) = 0 ∧ rc w (b₁ w) = 0 := by
      intro w
      have e := hi w
      rw [hb, RingHom.map_add, hθ', hθ', map_one, mul_one] at e
      have e1 := congrArg Complex.re e
      have e2 := congrArg Complex.im e
      rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, Complex.zero_im] at e2
      have e3 := (mul_eq_zero.1 e2).resolve_right (hδ _)
      rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, e3, zero_mul, add_zero, Complex.zero_re] at e1
      exact ⟨e1, e3⟩
    have z0 : b₀ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).1
    have z1 : b₁ = 0 := funext fun w => (rc w).map_eq_zero_iff.1 (key w).2
    rw [z0, z1, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero] at hb
    have hp : pairE (infPartF F E a) (finPartF F E a) = a := pairE_eta a
    rw [← hp, hb, hf]
    simp [pairE]

theorem exists_chartF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  intro F E _ _ _ _ _ σ B hB θ hθ
  refine exists_chart_of_cm hB.cm (fun w => (B.emb w).1) (fun w => ?_) θ hθ
  show InfinitePlace.mk ((B.emb w).1.comp (algebraMap F E)) = w
  rw [(B.emb w).2, InfinitePlace.mk_embedding]

end GlobalTheory.RealWeilF.CMChart

end
