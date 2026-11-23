import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LinkedUnlOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg

private theorem l_ne {l : ℕ} [Fact l.Prime] : ((l : ℕ) : PadicAlgCl l) ≠ 0 :=
  Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

private theorem adic_of_cont {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {D : Type} [TopologicalSpace D]
    (f : D → c.O) (hf : Continuous fun s => (f s).1) : AdicCont (maximalIdeal c.O) f := by
  intro N
  have hl : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  rw [IsLocallyConstant.iff_eventually_eq]
  intro s
  have hpos : 0 < ‖((l : ℕ) : PadicAlgCl l) ^ N‖ := norm_pos_iff.2 (pow_ne_zero _ l_ne)
  have hc : Continuous fun t => ‖(f t).1 - (f s).1‖ := (hf.sub continuous_const).norm
  have hev : ∀ᶠ t in nhds s, ‖(f t).1 - (f s).1‖ < ‖((l : ℕ) : PadicAlgCl l) ^ N‖ :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa using hpos)
  filter_upwards [hev] with t ht
  obtain ⟨z, hz⟩ := GlobalTheory.CoefCoord.exists_eq_pow_mul c N (f t - f s) ht.le
  rw [Ideal.Quotient.eq, hz]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl N)

private theorem clear_one {l : ℕ} [Fact l.Prime] (c : Coef l) {D : Type} [TopologicalSpace D] [CompactSpace D]
    (u : D → PadicAlgCl l) (hu : Continuous u)
    (h : ∀ s, ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * u s = a.1) :
    ∃ M : ℕ, ∀ s, (l : PadicAlgCl l) ^ M * u s ∈ c.O := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
  have hC1 : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hC1) (GlobalTheory.CoefCoord.norm_natCast_lt_one (l := l))
  refine ⟨M, fun s => ?_⟩
  have h1 : ‖(l : PadicAlgCl l) ^ M * u s‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc _ ≤ (max C 1)⁻¹ * max C 1 :=
          mul_le_mul hM.le ((hC s (Set.mem_univ s)).trans (le_max_left _ _)) (norm_nonneg _) (inv_pos.2 hC1).le
      _ = 1 := inv_mul_cancel₀ hC1.ne'
  obtain ⟨k, a, ha⟩ := h s
  have h2 : (((l : c.O) ^ M * a : c.O) : PadicAlgCl l) = (l : PadicAlgCl l) ^ k * ((l : PadicAlgCl l) ^ M * u s) := by
    push_cast
    rw [← ha]
    ring
  obtain ⟨z, hz⟩ := GlobalTheory.CoefCoord.exists_eq_pow_mul c k ((l : c.O) ^ M * a) (by
    rw [h2, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) h1)
  rw [hz] at h2
  push_cast at h2
  rw [← mul_left_cancel₀ (pow_ne_zero k l_ne) h2]
  exact z.2

theorem UpperTheory.V.Z.J.clearDen :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] {D : Type} [TopologicalSpace D] [CompactSpace D] (u β : D → PadicAlgCl l), Continuous u → Continuous β → (∀ s, ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * u s = a.1) → (∀ s, ∃ (m : ℕ) (a : c.O), (l : PadicAlgCl l) ^ m * β s = a.1) → ∃ (m : ℕ) (u' β' : D → c.O), AdicCont (IsLocalRing.maximalIdeal ↥c.O) u' ∧ AdicCont (IsLocalRing.maximalIdeal ↥c.O) β' ∧ (∀ s, (u' s).1 = (l : PadicAlgCl l) ^ m * u s) ∧ ∀ s, (β' s).1 = (l : PadicAlgCl l) ^ m * β s := by
  intro l _ c _ D _ _ u β hu hβ h1 h2
  obtain ⟨M, hM⟩ := clear_one c u hu h1
  obtain ⟨N, hN⟩ := clear_one c β hβ h2
  have hl : ∀ k : ℕ, (l : PadicAlgCl l) ^ k ∈ c.O := fun k => pow_mem (natCast_mem c.O l) k
  have a1 : ∀ s, (l : PadicAlgCl l) ^ (M + N) * u s ∈ c.O := fun s => by
    rw [add_comm, pow_add, mul_assoc]
    exact mul_mem (hl N) (hM s)
  have a2 : ∀ s, (l : PadicAlgCl l) ^ (M + N) * β s ∈ c.O := fun s => by
    rw [pow_add, mul_assoc]
    exact mul_mem (hl M) (hN s)
  exact ⟨M + N, fun s => ⟨_, a1 s⟩, fun s => ⟨_, a2 s⟩,
    adic_of_cont c _ (continuous_const.mul hu), adic_of_cont c _ (continuous_const.mul hβ),
    fun _ => rfl, fun _ => rfl⟩
