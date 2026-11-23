import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowSmulMemLattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_pow_mul_mem_O [IsNonarchimedeanLocalField F] (L : LocE F E)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by
  haveI : IsFractionRing 𝒪[F] F := (Valuation.integer.integers (valuation F)).isFractionRing
  haveI : Module.Free F E := L.free
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨⟨m, hm⟩, hmc⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) c hc
  have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hm0 hϖ
  refine ⟨k, (L.O_def _).2 ?_⟩
  have h2 : IsIntegral 𝒪[F] ((u : 𝒪[F]) • (m • c)) := hmc.smul _
  convert h2 using 1
  have e1 : (ϖ : F) ^ k = ((ϖ ^ k : 𝒪[F]) : F) := by push_cast; rfl
  rw [e1, ← hu, smul_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E, mul_comm u.1 m]
  rfl

theorem exists_pow_smul_mem_of_isLat [IsNonarchimedeanLocalField F] (L : LocE F E)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {n : ℕ} (Λ : Submodule L.O (Fin n → E))
    (hΛ : GlobalTheory.HL.IsLat L Λ) (y : Fin n → E) :
    ∃ m : ℕ, (algebraMap F E : F → E) ((ϖ : F) ^ m) • y ∈ Λ := by
  have hpowO : ∀ j : ℕ, algebraMap F E ((ϖ : F) ^ j) ∈ L.O := by
    intro j
    refine (L.O_def _).2 ?_
    have : algebraMap F E ((ϖ : F) ^ j) = algebraMap 𝒪[F] E (ϖ ^ j) := by
      rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; push_cast; rfl
    rw [this]; exact isIntegral_algebraMap
  have hsm : ∀ j : ℕ, ∀ x ∈ Λ, algebraMap F E ((ϖ : F) ^ j) • x ∈ Λ := by
    intro j x hx
    exact Λ.smul_mem (⟨_, hpowO j⟩ : L.O) hx
  have hy : y ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    refine ⟨i + j, ?_⟩
    have e : algebraMap F E ((ϖ : F) ^ (i + j)) • (a + b) =
        algebraMap F E ((ϖ : F) ^ j) • (algebraMap F E ((ϖ : F) ^ i) • a) +
        algebraMap F E ((ϖ : F) ^ i) • (algebraMap F E ((ϖ : F) ^ j) • b) := by
      simp only [smul_add, smul_smul, ← map_mul, ← pow_add]
      rw [add_comm j i]
    rw [e]
    exact Λ.add_mem (hsm j _ hi) (hsm i _ hj)
  | smul c x _ hx =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_O L ϖ hϖ c
    refine ⟨k + i, ?_⟩
    have e : algebraMap F E ((ϖ : F) ^ (k + i)) • (c • x) =
        (algebraMap F E ((ϖ : F) ^ k) * c) • (algebraMap F E ((ϖ : F) ^ i) • x) := by
      simp only [smul_smul, pow_add, map_mul]
      ring_nf
    rw [e]
    exact Λ.smul_mem (⟨_, hk⟩ : L.O) hi

end GlobalTheory.PowSmulMemLattice

end
