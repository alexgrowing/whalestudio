import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CMAdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ β : E, σ β ≠ β := by
  by_contra hne
  push Not at hne
  have := h.2.1
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext y
  have := h.2.2.2 τ y
  rw [hne y] at this
  simpa using this.symm

theorem im_ne_zero {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) (τ : E →+* ℂ) : (τ β).im ≠ 0 := by
  intro h0
  apply hβ
  apply τ.injective
  rw [h.2.2.2 τ β]
  exact Complex.conj_eq_iff_im.2 h0

theorem exists_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {β : E} (hβ : σ β ≠ β) :
    ∃ B : Module.Basis (Fin 2) F E, B 0 = 1 ∧ B 1 = β := by
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hβ
      have e : β = algebraMap F E (-(s / t)) := by
        have ht' : algebraMap F E t ≠ 0 := by simpa using ht
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_neg, map_div₀]
        field_simp
        linear_combination hst
      rw [e, AlgHom.commutes]
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h.2.2.1]), ?_, ?_⟩ <;> simp

theorem eq_add_tmul (B : Module.Basis (Fin 2) F E) (x : AF F ⊗[F] E) :
    x = (Algebra.TensorProduct.basis (AF F) B).repr x 0 ⊗ₜ[F] B 0 +
      (Algebra.TensorProduct.basis (AF F) B).repr x 1 ⊗ₜ[F] B 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF F) B).sum_repr x]
  simp [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem piInf_tmul {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) (a : AF F) (y : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ (a ⊗ₜ[F] y) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 y := rfl

theorem im_extension (hF : IsTotallyReal F) (w : InfinitePlace F) (z : w.Completion) :
    (InfinitePlace.Completion.extensionEmbedding w z).im = 0 := by
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w) z]
  exact Complex.ofReal_im _

theorem eq_zero_of_piInf : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) x → (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w) x = 0) → x = 0 := by
  intro F E _ _ _ _ _ σ h emb x hx hinf
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨B, hB0, hB1⟩ := exists_basis h hβ
  have hdec := eq_add_tmul B x
  set C := Algebra.TensorProduct.basis (AF F) B with hC
  have hu : pairA F 0 1 • x = 0 := hx _ (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hfin : ∀ i, (C.repr x i).2 = 0 := fun i => by
    have h1 : C.repr (pairA F 0 1 • x) i = 0 := by rw [hu]; simp
    rw [map_smul] at h1
    have h2 : pairA F 0 1 * C.repr x i = 0 := h1
    have h3 := congrArg (sndA F) h2
    rw [map_mul, map_zero] at h3
    exact (one_mul _).symm.trans h3
  have hre : ∀ w i, (C.repr x i).1 w = 0 := fun w => by
    have e := hinf w
    rw [hdec, map_add, piInf_tmul, piInf_tmul, hB0, hB1, map_one, mul_one] at e
    have hi := congrArg Complex.im e
    have him := im_ne_zero h hβ (emb w).1
    set p := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 0).1 w) with hp
    set q := InfinitePlace.Completion.extensionEmbedding w ((C.repr x 1).1 w) with hq
    have hpi : p.im = 0 := im_extension h.1 w _
    have hqi : q.im = 0 := im_extension h.1 w _
    simp only [Complex.add_im, Complex.mul_im, Complex.zero_im, hpi, hqi, zero_mul, add_zero, zero_add] at hi
    have hq0 : q.re = 0 := (mul_eq_zero.1 hi).resolve_right him
    have hq1 : q = 0 := Complex.ext hq0 hqi
    rw [hq1, zero_mul, add_zero] at e
    have inj := (InfinitePlace.Completion.extensionEmbedding w).injective
    intro i
    fin_cases i
    · show (C.repr x 0).1 w = 0
      exact inj (e.trans (map_zero _).symm)
    · show (C.repr x 1).1 w = 0
      exact inj (hq1.trans (map_zero _).symm)
  have hz : C.repr x = 0 := by
    ext i
    show C.repr x i = 0
    exact Prod.ext (funext fun w => hre w i) (hfin i)
  simpa using hz

end GlobalTheory.CompanionTheory.CMAdele

end
