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

theorem natCast_isUnit_ae {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (N : ℕ) (hN : N ≠ 0) :
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  have hx : ((N : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {((N : 𝓞 F))} ≠ ⊥ := by simpa using hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation F (N : F) = 1 := by
    have : ((N : F)) = algebraMap (𝓞 F) F (N : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hmem
  have hι : (A.loc p).ιF (N : F) = (N : (A.loc p).Fp) := map_natCast _ _
  have h1 : (N : (A.loc p).Fp) ≤ᵥ 1 := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have h2 : (1 : (A.loc p).Fp) ≤ᵥ (N : (A.loc p).Fp) := by
    rw [← hι, ← map_one (A.loc p).ιF, (A.loc p).val, hv, map_one]
  have hmem1 : (N : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff]; exact (Valuation.vle_one_iff (v := valuation _)).1 h1
  have hN0 : (N : (A.loc p).Fp) ≠ 0 := by
    haveI := (A.loc p).char0; exact Nat.cast_ne_zero.2 hN
  have hmem2 : (N : (A.loc p).Fp)⁻¹ ∈ 𝒪[(A.loc p).Fp] := by
    rw [Valuation.mem_integer_iff, map_inv₀, inv_le_one₀]
    · have := (Valuation.vle_iff_le (v := valuation _)).1 h2; rwa [map_one] at this
    · exact (Valuation.pos_iff _).2 hN0
  refine ⟨⟨⟨_, hmem1⟩, ⟨_, hmem2⟩, ?_, ?_⟩, rfl⟩
  · ext; simp [mul_inv_cancel₀ hN0]
  · ext; simp [inv_mul_cancel₀ hN0]

end GlobalTheory.HL.Glue
