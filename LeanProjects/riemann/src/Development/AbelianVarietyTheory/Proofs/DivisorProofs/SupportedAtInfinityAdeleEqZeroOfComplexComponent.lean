import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionConjOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.AdeleInfInj

theorem eq_zero_of_piInf_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  intro F E _ _ _ _ _ σ cm emb z hz hinf
  have hx : ∃ x : E, x ∉ Set.range (algebraMap F E) := by
    by_contra hc
    push_neg at hc
    have h0 : (⊥ : Subalgebra F E) = ⊤ := eq_top_iff.2 fun y _ => Algebra.mem_bot.2 (hc y)
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h0
    rw [cm.2.2.1] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨x, hx0⟩ := hx
  have li : LinearIndependent F ![(1 : E), x] := LinearIndependent.pair_iff.2 fun s t hst => by
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hx0
      refine ⟨-(s / t), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      rw [map_neg, map_div₀, neg_div', div_eq_iff htE]
      linear_combination -hst
  let b : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank li (by simp [cm.2.2.1])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = x := by simp [b]
  have him : ∀ τ : E →+* ℂ, (τ x).im ≠ 0 := fun τ h0 => by
    have hσx : σ x = x := τ.injective (by
      rw [cm.2.2.2]
      exact Complex.conj_eq_iff_im.2 h0)
    have hσ : ∀ y, σ y = y := by
      intro y
      have e := b.ext (f₁ := σ.toLinearMap) (f₂ := LinearMap.id) fun i => by
        fin_cases i
        · simp [hb0]
        · simp [hb1, hσx]
      exact LinearMap.congr_fun e y
    have := cm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => ?_)))
    exact (cm.2.2.2 τ y).symm.trans (by rw [hσ y])
  let bA := Algebra.TensorProduct.basis (AF F) b
  have hz_eq : z = ∑ i, bA.repr z i ⊗ₜ[F] b i := by
    conv_lhs => rw [← bA.sum_repr z]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have hfin : ∀ i, (bA.repr z i).2 = 0 := fun i => by
    have h1 : bA.repr (u • z) i = u * bA.repr z i := by rw [map_smul]; rfl
    rw [hz u (map_zero _), map_zero, Finsupp.zero_apply] at h1
    have h3 : (0 : Af F) = 1 * (bA.repr z i).2 := congrArg Prod.snd h1
    simpa using h3.symm
  have := cm.1
  have hinf' : ∀ w i, evInf F w (bA.repr z i) = 0 := fun w => by
    have hw := IsTotallyReal.isReal w
    have h := hinf w
    rw [hz_eq, map_sum, Fin.sum_univ_two] at h
    change InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 0)) * (emb w).1 (b 0) +
      InfinitePlace.Completion.extensionEmbedding w (evInf F w (bA.repr z 1)) * (emb w).1 (b 1) = 0 at h
    rw [hb0, hb1, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw] at h
    set r0 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 0)) with hr0
    set r1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (evInf F w (bA.repr z 1)) with hr1
    have h1 : r1 = 0 := by
      have := congrArg Complex.im h
      simp at this
      exact this.resolve_right (him _)
    have h0 : r0 = 0 := by
      have := congrArg Complex.re h
      simpa [h1] using this
    intro i
    fin_cases i
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h0.trans (map_zero _).symm)
    · exact (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw).injective (h1.trans (map_zero _).symm)
  have hc : ∀ i, bA.repr z i = 0 := fun i => Prod.ext (funext fun w => hinf' w i) (hfin i)
  rw [hz_eq]
  simp [hc]

end GlobalTheory.AdeleInfInj
