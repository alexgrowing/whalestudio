import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.CMTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hr : w.IsReal := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    simp only [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 w.embedding x
    rw [hc x] at this
    exact this.symm
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr (h.2.1.isComplex w)) hr

def sigE {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Gal(E/F) :=
  AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun x => sig_sig h x) (AlgHom.ext fun x => sig_sig h x)

theorem trace_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  have hne : (1 : Gal(E/F)) ≠ sigE h := by
    intro h1
    obtain ⟨x, hx⟩ := sig_ne_id h
    exact hx (congrArg (fun g : Gal(E/F) => g x) h1).symm
  have hle : Nat.card Gal(E/F) ≤ 2 := by
    calc Nat.card Gal(E/F) ≤ Nat.card (E →ₐ[F] E) :=
          Nat.card_le_card_of_injective (fun g => (g : E →ₐ[F] E)) (fun a b hab => AlgEquiv.coe_algHom_injective hab)
      _ ≤ Module.finrank F E := card_algHom_le_finrank F E E
      _ = 2 := h.2.2.1
  have hall : ∀ g : Gal(E/F), g = 1 ∨ g = sigE h := by
    classical
    have hc : (({1, sigE h} : Finset Gal(E/F))).card = 2 := Finset.card_pair hne
    have hu : ({1, sigE h} : Finset Gal(E/F)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc]
      rw [← Nat.card_eq_fintype_card]
      have : 2 ≤ Nat.card Gal(E/F) := by
        rw [Nat.card_eq_fintype_card, ← hc]; exact Finset.card_le_univ _
      omega
    intro g
    have := Finset.mem_univ g
    rw [← hu] at this
    simpa using this
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [h.2.2.1]
    apply le_antisymm hle
    classical
    rw [Nat.card_eq_fintype_card, ← Finset.card_pair hne]
    exact Finset.card_le_univ _
  rw [trace_eq_sum_automorphisms]
  classical
  rw [Fintype.sum_eq_add 1 (sigE h) hne (fun g hg => absurd (hall g) (by tauto))]
  rfl

end GlobalTheory.CMTrace

namespace GlobalTheory.CMTrace

theorem adele_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : AF F, Algebra.trace (AF F) (AE F E) (algebraMap (AF F) (AE F E) x) = 2 * x) ∧ ∀ c : AE F E, algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) c) = c + cA σ c := by
  intro F E _ _ _ _ _ σ h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  refine ⟨fun x => ?_, fun c => ?_⟩
  · rw [Algebra.trace_algebraMap, Module.finrank_baseChange, h.2.2.1, nsmul_eq_mul, Nat.cast_ofNat]
  · have htm : ∀ (a : AF F) (e : E), Algebra.trace (AF F) (AE F E) (a ⊗ₜ[F] e) =
        a * algebraMap F (AF F) (Algebra.trace F E e) := by
      intro a e
      have h1 : a ⊗ₜ[F] e = a • ((1 : AF F) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; abel
    | tmul a e =>
      rw [htm, Algebra.TensorProduct.algebraMap_apply, cA, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        ← TensorProduct.tmul_add, ← trace_eq h, mul_comm, ← Algebra.smul_def, Algebra.algebraMap_self,
        RingHom.id_apply, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

end GlobalTheory.CMTrace
