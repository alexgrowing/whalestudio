import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.NormOneField

open Polynomial in

theorem normOneGen_of_imag {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (hinv : ∀ a : R, a ≠ 0 → ∃ b, a * b = 1) (c : R →+* R) (θ : R) (hθ : θ ≠ 0) (hc : c θ = -θ) :
    NormOneGen c := by
  have hU : ∀ a : R, a ≠ 0 → IsUnit a := fun a ha => by
    obtain ⟨b, hb⟩ := hinv a ha
    exact isUnit_iff_exists_inv.2 ⟨b, hb⟩
  intro α p hα _
  by_cases hp : p = 0
  · subst hp
    refine ⟨1, by simp, by simpa using hα, ?_⟩
    simpa using (hU 2 two_ne_zero).mul hα
  have hne : ∀ n : ℕ, (n : R) - θ ≠ 0 := by
    intro n h
    have e : θ = n := (sub_eq_zero.1 h).symm
    have h1 : c θ = θ := by
      rw [e, map_natCast]
    have h2 : (2 : R) * θ = 0 := by linear_combination hc - h1
    exact hθ ((mul_eq_zero.1 h2).resolve_left two_ne_zero)
  choose i hi using fun n : ℕ => hinv _ (hne n)
  set m : ℕ → R := fun n => ((n : R) + θ) * i n with hm
  have hnorm : ∀ n, m n * c (m n) = 1 := by
    intro n
    have h1 : c (((n : R) - θ) * i n) = 1 := by rw [hi, map_one]
    rw [map_mul, map_sub, map_natCast, hc] at h1
    simp only [hm, map_mul, map_add, map_natCast, hc]
    linear_combination (((n : R) - -θ) * c (i n)) * hi n + h1
  have hminj : Function.Injective m := by
    intro a b h
    have h' : ((a : R) + θ) * i a = ((b : R) + θ) * i b := h
    have h1 : ((a : R) + θ) * ((b : R) - θ) = ((b : R) + θ) * ((a : R) - θ) := by
      linear_combination ((a : R) - θ) * ((b : R) - θ) * h' - ((a : R) + θ) * ((b : R) - θ) * hi a +
        ((b : R) + θ) * ((a : R) - θ) * hi b
    have h2 : ((2 : R) * ((b : R) - a)) * θ = 0 := by linear_combination h1
    have h3 : (b : R) - a = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hθ)).resolve_left two_ne_zero
    exact (Nat.cast_injective (R := R) (sub_eq_zero.1 h3)).symm
  set q : R[X] := X ^ 2 - C (2 * α) * X + C (p * c p) with hq
  have hq0 : q ≠ 0 := by
    intro h
    have h2 := congrArg (fun r => r.coeff 2) h
    simp [hq, coeff_X, coeff_C] at h2
  have hY : ({α} ∪ {y | q.IsRoot y} : Set R).Finite :=
    (Set.finite_singleton α).union (Polynomial.finite_setOf_isRoot hq0)
  have hg : Function.Injective (fun n => m n * p) := fun a b h =>
    hminj (mul_right_cancel₀ hp h)
  obtain ⟨n, hn⟩ := (hY.preimage hg.injOn).exists_notMem
  refine ⟨m n, hnorm n, hU _ fun h => hn (Or.inl (sub_eq_zero.1 h).symm), hU _ fun h => hn (Or.inr ?_)⟩
  rw [map_mul] at h
  have h4 := hnorm n
  change q.IsRoot (m n * p)
  simp only [hq, IsRoot, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  linear_combination (-(m n * p)) * h - (p * c p) * h4

theorem exists_imag {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := hcm.2.1.isComplex w
  have hτ : ¬ ComplexEmbedding.IsReal w.embedding := InfinitePlace.isComplex_iff.1 hw
  have hx : ∃ x : E, σ x ≠ x := by
    by_contra h
    push Not at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hcm.2.2.2 w.embedding x
    rw [h x] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hx
  have hσσ : σ (σ x) = x := w.embedding.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  exact ⟨x - σ x, sub_ne_zero.2 hx.symm, by rw [map_sub, hσσ, neg_sub]⟩

theorem normOne_of_isField : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K], IsField (K ⊗[F] E) →
    NormOneGen (sigR K σ) := by
  intro F E _ _ _ _ _ σ hCM K _ _ hf
  haveI : Nontrivial (K ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  haveI : IsDomain (K ⊗[F] E) := hf.isDomain
  haveI : CharZero (K ⊗[F] E) :=
    charZero_of_injective_algebraMap (R := F) (algebraMap F (K ⊗[F] E)).injective
  obtain ⟨δ, hδ, hσδ⟩ := exists_imag hCM
  have hs : sigR K σ (inclR K δ) = inclR K (σ δ) := by
    simp [sigR, inclR]
  refine normOneGen_of_imag (fun a ha => hf.mul_inv_cancel ha) (sigR K σ) (inclR K δ) ?_ ?_
  · intro h
    have h1 : inclR (F := F) K (δ * δ⁻¹) = 0 := by rw [map_mul, h, zero_mul]
    rw [mul_inv_cancel₀ hδ, map_one] at h1
    exact one_ne_zero h1
  · rw [hs, hσδ, map_neg]

end GlobalTheory.CompanionTheory.SaGen.NormOneField
