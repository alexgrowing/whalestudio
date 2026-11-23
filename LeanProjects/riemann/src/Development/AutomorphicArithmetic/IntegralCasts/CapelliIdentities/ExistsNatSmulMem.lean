import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

private theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_den {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ (M : ℕ) (a : NumberField.RingOfIntegers K), 0 < M ∧ (M : K) * c = a := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hi⟩ := hc.exists_integral_multiple
  have h2 : IsIntegral ℤ (y • y • c) := hi.smul y
  refine ⟨(y * y).natAbs, ⟨_, h2⟩, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have : (((y * y).natAbs : ℕ) : K) = ((y * y : ℤ) : K) := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
  rw [this]
  change _ = y • y • c
  simp [mul_assoc]

private theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.core {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {Λ : Submodule (NumberField.RingOfIntegers K) V}
    (h : Submodule.span K (Λ : Set V) = ⊤) (x : V) :
    ∃ N : ℕ, 0 < N ∧ (N : K) • x ∈ Λ := by
  have hn : ∀ (M : ℕ) (v : V), v ∈ Λ → (M : K) • v ∈ Λ := fun M v hv => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv M
  have hx : x ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_pos, hn 1 v hv⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N, hN, hu⟩ := hu
    obtain ⟨M, hM, hv⟩ := hv
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : K) • (u + v) = (M : K) • (N : K) • u + (N : K) • (M : K) • v := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (M : K)]
    rw [this]
    exact Λ.add_mem (hn _ _ hu) (hn _ _ hv)
  | smul c v _ hv =>
    obtain ⟨N, hN, hv⟩ := hv
    obtain ⟨M, a, hM, ha⟩ := UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_den c
    refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
    have : ((N * M : ℕ) : K) • c • v = a • (N : K) • v := by
      rw [← algebraMap_smul K a, smul_smul, smul_smul, Nat.cast_mul, mul_assoc, ha, mul_comm]
    rw [this]
    exact Λ.smul_mem a hv

theorem UpperTheory.Reformulated.B.ExistsNatSmulMem.exists_nat_smul_mem :
    ∀ {D : Formalism.BasicNotions.D7} {n : ℕ}
    {Λ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E)},
    Submodule.IsLattice D.host.E Λ →
      ∀ (x : Fin n → D.host.E),
        ∃ (N : ℕ),
          (0 : ℕ) < N ∧
            (↑N : D.host.E) • x ∈
              Λ := by
  intro D n Λ h x
  exact UpperTheory.Reformulated.B.ExistsNatSmulMem.core h.span_eq_top x
