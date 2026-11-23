import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationOfDerivationOnLargeSubalgebra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsZetaDerivationInertiaCyclotomicAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebraStatement

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem pow_four_mul_mem_of_smul_dA_eq_zero : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (N : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ N) → ∀ a : A, a • dA A z = 0 → ∃ w ∈ A, (l : Ω) ^ 4 * (a : Ω) = (l : Ω) ^ N * w := by
  intro l _ hl2 Ω _ _ _ A hA N z hz a hrel
  have hlΩ : (l : Ω) ≠ 0 := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hpos : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  have hz1 : (z : Ω) ^ (l ^ N) = 1 := hz.pow_eq_one
  have hzA : z ^ (l ^ N) = 1 := Subtype.ext (by simpa using hz1)
  have hzT : z ∈ cycAlg l A := mem_cycAlg_of_pow hzA
  have hrel' : ∑ i : Fin 1, (fun _ => a) i •
      KaehlerDifferential.D (fixA A) A ((fun _ => z) i) = 0 := by
    simpa using hrel
  obtain ⟨F, hF⟩ := kaehler_rel_local (fixA A) A 1 _ _ hrel'
  obtain ⟨C, tr, m, α, β, hFC, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA F
  obtain ⟨D, hD, hDv⟩ := GlobalTheory.T.exists_zeta_derivation_inertia_cyclotomic_algebra l Ω A hA N z hz
  obtain ⟨D', hD', hD'v⟩ := exists_derOn_ext (fixA A) A (FracA A) (cycAlg l A) C tr m α β _ htr D hD
  have h := hF C hFC (fun _ => htr.le hzT) (FracA A) D' hD'
  rw [Fin.sum_univ_one, hD'v _ hzT, hDv, smul_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨t, ht⟩ := h
  have ht' : (t : Ω) = (a : Ω) * (l : Ω) ^ 3 * ((z : Ω) * (l : Ω) / (l : Ω) ^ N) := by
    simpa [Algebra.smul_def] using ht
  refine ⟨((t * z ^ (l ^ N - 1) : A) : Ω), (t * z ^ (l ^ N - 1)).2, ?_⟩
  have hzz : (z : Ω) * (z : Ω) ^ (l ^ N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, hz1]
  push_cast
  rw [ht']
  field_simp
  linear_combination (-((a : Ω))) * hzz

end GlobalTheory.RecOne
