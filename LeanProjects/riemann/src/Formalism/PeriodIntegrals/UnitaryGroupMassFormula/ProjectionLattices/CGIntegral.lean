import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.FinrankIntertw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.IsIntegralTraceOfPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.MajAtZeroRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionLattices.StarMapTraceOfPowEqOne

noncomputable section

namespace PI.Dv.GLP

open NumberField

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cG (T : GoodSet K G) (x : G) : K := ∑ s, cS T s x

theorem asAlg_eG {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (T : GoodSet K G) : ρ.asAlgebraHom (eG T) = ∑ x : G, cG T x • ρ x := by
  rw [eG, map_sum]
  simp_rw [asAlg_eS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cG, Finset.sum_smul]

theorem cG_integral [CharZero K] (T : GoodSet K G) (x : G) :
    IsIntegral ℤ (((Fintype.card G : ℕ) : K) * cG T x) := by
  have h : ((Fintype.card G : ℕ) : K) * cG T x =
      ∑ s, ((Module.finrank K (T.W s) : ℕ) : K) * LinearMap.trace K _ (T.tau s x⁻¹) := by
    rw [cG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have := card_ne_zero (K := K) (G := G)
    rw [cS]
    field_simp
  rw [h]
  refine IsIntegral.sum _ fun s _ => ?_
  refine IsIntegral.mul ?_ ?_
  · have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K ((Module.finrank K (T.W s) : ℕ) : ℤ)))
    simpa using this
  · exact isIntegral_trace_of_pow _ (Fintype.card G) Fintype.card_pos
      (by rw [← map_pow, pow_card_eq_one, map_one])

theorem star_cG (σ : K →+* ℂ) (T : GoodSet K G) (g : G) :
    star (σ (cG T g)) = σ (cG T g⁻¹) := by
  simp only [cG, cS, map_sum, map_mul, map_div₀, map_natCast, star_sum, star_mul', star_div₀,
    star_natCast, PI.Dv.GLPTr.star_map_trace_rep, inv_inv]

theorem glatProj : PI.Dv.GLatProj := by
  intro K _ _ _ _ G _ _ T A ρ hA
  obtain ⟨hgood, hL, hnorm⟩ := hA
  refine ⟨hgood, Fintype.card_pos, ?_, ?_, ?_⟩
  · rw [← map_mul, eG_mul_eG]
  · intro y hy
    rw [asAlg_eG]
    have hz : ∀ x : G, ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = ((Fintype.card G : ℕ) : K) * cG T x :=
      fun x => ⟨⟨_, cG_integral T x⟩, rfl⟩
    choose a ha using hz
    have h1 : (((Fintype.card G : ℕ) : 𝓞 K)) • (∑ x : G, cG T x • ρ x) y =
        ∑ x : G, a x • ρ x y := by
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K, LinearMap.sum_apply, Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [LinearMap.smul_apply, smul_smul, ← ha, algebraMap_smul]
    rw [h1]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hL x y hy)
  · intro v x y
    rw [asAlg_eG]
    exact majAt_selfadj' A.b A.X v ρ (fun g z => hnorm g v z) (cG T)
      (fun g => star_cG v.embedding T g) x y

end PI.Dv.GLP
