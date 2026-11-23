import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.MonoCount

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem sum_mon_le (hM : MonoCount) (D : D7) (j T n : ℕ) :
    ∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * n ≤ Nat.choose (T - 1) (WeightFamilies.dimY D j) * n := by
  rw [← Finset.sum_mul]
  by_cases h : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ h]
  · have h0 : a0 D j T = 0 := by
      show T - WeightFamilies.dimY D j = 0
      omega
    simp [h0]

theorem lenBase_of (hF : FiltLenGr) (hM : MonoCount) (hK : FkFilt) (hG : GrBound) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) := by
  intro D B P j X ka wL wF G la Q S CRm T c hOk hth hw hI
  obtain ⟨hA, h0, hT⟩ := hK G la T
  obtain ⟨φ, Pk, Qk, hker, hP, hQ, hL⟩ := hG G la Q S CRm T c hOk hth hw hI
  have key := hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) hA h0 hT
    (fun _ => Vg G la) φ hker (Q.AA T) (firstLength_le_prime_bound G la T ⊓ Q.AA T) Pk Qk inf_le_right hP hQ
  have e : (firstLength_le_prime_bound G la T ⊓ Q.AA T).comap (Q.AA T).subtype = (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype := by
    ext x
    simp [x.2]
  rw [e] at key
  refine key.trans ?_
  calc ∑ k ∈ Finset.range (a0 D j T), Module.length (Op X la G.N) (↥(Pk k) ⧸ (Qk k).comap (Pk k).subtype)
      ≤ ∑ k ∈ Finset.range (a0 D j T), ((((mon D j k).card * Q.Ila.toNat : ℕ)) : ℕ∞) :=
        Finset.sum_le_sum fun k hk => hL k (Finset.mem_range.1 hk)
    _ = ((∑ k ∈ Finset.range (a0 D j T), (mon D j k).card * Q.Ila.toNat : ℕ) : ℕ∞) := by
        push_cast; rfl
    _ ≤ _ := by exact_mod_cast sum_mon_le hM D j T Q.Ila.toNat

end PoleLengthBounds
