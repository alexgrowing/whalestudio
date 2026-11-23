import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRat

theorem sum_cmType_eq_trace {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Fintype ι] (h2 : Module.finrank F E = 2) (τ : ι → (E →+* ℂ)) (hi : Function.Injective τ)
    (hcm : ∀ σ, (∃ t, τ t = σ) ↔ ¬ ∃ t, τ t = ComplexEmbedding.conjugate σ) (x : F)
    (hx : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate σ (algebraMap F E x) = σ (algebraMap F E x)) :
    ∑ t, τ t (algebraMap F E x) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  classical
  set y := algebraMap F E x with hy
  have h1 : ((Algebra.trace ℚ E y : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ y := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := y)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ fun _ => rfl).symm
  have h3 : Algebra.trace ℚ E y = 2 * Algebra.trace ℚ F x := by
    rw [← Algebra.trace_trace (S := F), hy, Algebra.trace_algebraMap, h2, map_nsmul, nsmul_eq_mul]
    rfl
  have hb : Function.Bijective (Sum.elim τ fun t => ComplexEmbedding.conjugate (τ t)) := by
    have hc : ∀ σ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (τ b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (τ a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, τ t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : E →+* ℂ => σ y
  rw [Fintype.sum_sum_type, ← h1, h3] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, hx] at h4
  push_cast at h4
  linear_combination h4 / 2

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_tauE_eq_trace (D : D7) (x : D.host.F) :
    ∑ t, tauE D t (algebraMap D.host.F D.host.E x) = ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ) := by
  have hcm := D.host.isCMField_hostE
  refine sum_cmType_eq_trace ?_ _ (tauE_injective D) (tauE_cm D) x fun σ => ?_
  · exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  · show starRingEnd ℂ (σ _) = _
    rw [← IsCMField.complexEmbedding_complexConj]
    exact congrArg σ ((IsCMField.complexConj D.host.E).commutes x)

theorem char_fin_rat {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (h : IsCharAF F ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) = psiInf F ψ (algebraMap F (Ainf F) (-x)) := by
  have e : pairA F 0 (algebraMap F (Af F) x) =
      algebraMap F (AF F) x + pairA F (algebraMap F (Ainf F) (-x)) 0 := by
    refine Prod.ext ?_ (add_zero _).symm
    show (0 : Ainf F) = algebraMap F (Ainf F) x + algebraMap F (Ainf F) (-x)
    rw [map_neg, add_neg_cancel]
  rw [e, AddChar.map_add_eq_mul, h.2.2.1, one_mul, psiInf]

theorem tmul_one_eq {F E A : Type} [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A] (x : F) :
    (algebraMap F A x) ⊗ₜ[F] (1 : E) = (1 : A) ⊗ₜ[F] (algebraMap F E x) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem stdChar_fin_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ x : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) x)) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.F x : ℚ) : ℂ)) := by
  intro D ψ hψ x
  obtain ⟨θ, hθ⟩ := hψ.2.1
  rw [char_fin_rat ψ hψ.1, hψ.2.2 θ hθ, tmul_one_eq,
    Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, sum_tauE_eq_trace, map_neg]
  congr 1
  push_cast
  ring

end GlobalTheory.StdRat

end
