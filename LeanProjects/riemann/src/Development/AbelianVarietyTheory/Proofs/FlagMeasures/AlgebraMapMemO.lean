import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

open ValuativeRel

namespace GlobalTheory.CommonDenominator

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem algebraMap_mem_O (L : Formalism.MainNotions.S.Loc.LocE F E) (t : 𝒪[F]) :
    algebraMap F E (t : F) ∈ L.O := by
  rw [L.O_def]
  have h : algebraMap F E (t : F) = algebraMap 𝒪[F] E t := by
    rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [h]
  exact isIntegral_algebraMap

theorem exists_den (L : Formalism.MainNotions.S.Loc.LocE F E) (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E (t : F) * c ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have hc : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) c hc
  refine ⟨(m : 𝒪[F]), nonZeroDivisors.ne_zero m.2, ?_⟩
  rw [L.O_def]
  have h : m • c = algebraMap F E ((m : 𝒪[F]) : F) * c := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E]; rfl
  rw [← h]
  exact hm

theorem main (L : Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} [IsNonarchimedeanLocalField F]
    {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)} (hΛ : GlobalTheory.HL.IsLat L Λ)
    (x : Fin n → E) :
    ∃ (t : ↥(Valuation.integer (ValuativeRel.valuation F))),
      t ≠ (0 : ↥(Valuation.integer (ValuativeRel.valuation F))) ∧
      (Algebra.algebraMap F E : F → E) (↑t : F) • x ∈ Λ := by
  have hx : x ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; exact Submodule.mem_top
  have key : ∀ (a : E) (ha : a ∈ L.O) (v : Fin n → E), v ∈ Λ → a • v ∈ Λ := by
    intro a ha v hv
    have := Λ.smul_mem (⟨a, ha⟩ : L.O) hv
    exact this
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t1, h1, hy⟩ := hy
    obtain ⟨t2, h2, hz⟩ := hz
    refine ⟨t1 * t2, mul_ne_zero h1 h2, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((t1 * t2 : 𝒪[F]) : F) • (y + z)
        = algebraMap F E (t2 : F) • (algebraMap F E (t1 : F) • y)
          + algebraMap F E (t1 : F) • (algebraMap F E (t2 : F) • z) := by
      simp only [Subring.coe_mul, map_mul, smul_add, smul_smul]
      rw [mul_comm (algebraMap F E (t2 : F)) (algebraMap F E (t1 : F))]
    rw [e]
    exact Λ.add_mem (key _ (algebraMap_mem_O L t2) _ hy) (key _ (algebraMap_mem_O L t1) _ hz)
  | smul c y _ hy =>
    obtain ⟨t, ht, hy⟩ := hy
    obtain ⟨s, hs, hsc⟩ := exists_den L c
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (Algebra.algebraMap F E : F → E) ((s * t : 𝒪[F]) : F) • (c • y)
        = (algebraMap F E (s : F) * c) • (algebraMap F E (t : F) • y) := by
      simp only [Subring.coe_mul, map_mul, smul_smul]
      rw [mul_right_comm]
    rw [e]
    exact key _ hsc _ hy

end GlobalTheory.CommonDenominator
