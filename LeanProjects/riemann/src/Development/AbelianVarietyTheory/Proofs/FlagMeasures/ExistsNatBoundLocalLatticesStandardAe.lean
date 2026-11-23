import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem exists_uniform_bound {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ)
    (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (hfin : {p | Λ p ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite)
    (hm : ∀ p, ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (m : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ p, (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • v ∈ Λ p) ∧ ∀ v ∈ Λ p, ∀ i, (N : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  choose m hm0 hm1 hm2 using hm
  refine ⟨∏ q ∈ hfin.toFinset, m q, Finset.prod_ne_zero_iff.mpr fun q _ => hm0 q, fun p => ?_⟩
  by_cases hp : p ∈ hfin.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hp
    rw [hk]
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · have h1 := hm1 p v hv
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) • v = k • ((m p : (A.loc p).Ep) • v) := by
        rw [← Nat.cast_smul_eq_nsmul (A.loc p).Ep, smul_smul]
        push_cast
        ring_nf
      rw [h2]
      exact nsmul_mem h1 k
    · have h1 := hm2 p v hv i
      have h2 : ((m p * k : ℕ) : (A.loc p).Ep) * v i = (k : (A.loc p).Ep) * ((m p : (A.loc p).Ep) * v i) := by
        push_cast; ring
      rw [h2]
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O k) h1
  · have hΛ : Λ p = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep)) := by
      by_contra h
      exact hp (hfin.mem_toFinset.mpr h)
    refine ⟨fun v hv => ?_, fun v hv i => ?_⟩
    · rw [hΛ, mem_span_single_iff]
      intro i
      have := (A.L p).O.mul_mem (natCast_mem (A.L p).O (∏ q ∈ hfin.toFinset, m q)) (hv i)
      simpa only [Pi.smul_apply, smul_eq_mul] using this
    · rw [hΛ, mem_span_single_iff] at hv
      exact (A.L p).O.mul_mem (natCast_mem (A.L p).O _) (hv i)

end GlobalTheory.HL.Glue
