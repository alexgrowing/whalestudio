import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDualIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.StdCharUnique

variable (F : Type) [Field F] [NumberField F]

theorem sum_mult_re_eq_trace (x : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings ℂ (K := ℚ) (L := F) (x := x)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ fun _ => rfl).symm
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← InfinitePlace.card_filter_mk_eq, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr (by congr) fun φ hφ => ?_
  have hw : InfinitePlace.mk φ = w := (Finset.mem_filter.1 hφ).2
  subst hw
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

theorem traceInf_add (x y : Ainf F) : traceInf F (x + y) = traceInf F x + traceInf F y := by
  rw [traceInf, traceInf, traceInf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [show (x + y) w = x w + y w from rfl, map_add, Complex.add_re, mul_add]

theorem continuous_traceInf : Continuous (traceInf F) := by
  refine continuous_finset_sum _ fun w _ => continuous_const.mul (Complex.continuous_re.comp ?_)
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem traceInf_algebraMap (x : F) :
    traceInf F (algebraMap F (Ainf F) x) = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  rw [← sum_mult_re_eq_trace, traceInf]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  exact InfinitePlace.Completion.extensionEmbedding_coe w _

theorem existsUnique_isStdChar : ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => (traceInf F x : ℂ)) fun a b => by
    rw [traceInf_add, Complex.ofReal_add]
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.StdAdelicChar.exists_char_of_trace F L
    (Complex.continuous_ofReal.comp (continuous_traceInf F)) fun x => by
      show ((traceInf F (algebraMap F (Ainf F) x) : ℝ) : ℂ) = _
      rw [traceInf_algebraMap, Complex.ofReal_ratCast]
  have hψ : IsStdChar F ψ := ⟨h1, fun x => by
    rw [h2, stdInf]
    congr 1
    show _ * ((traceInf F x : ℝ) : ℂ) = _
    push_cast
    ring⟩
  exact ⟨ψ, hψ, fun ψ' h' => GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h'.1 hψ.1
    fun x => (h'.2 x).trans (hψ.2 x).symm⟩

theorem existsUnique_isStdChar_cm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
      (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
      ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ :=
  fun F _ _ _ _ _ _ _ _ _ _ _ => existsUnique_isStdChar F

end GlobalTheory.StdCharUnique

end
