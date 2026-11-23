import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.primesex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem absorb (A N t e : ℝ) (k a : ℕ) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e + 1 ≤ t) :
    A * N * (N * (e + 1)) ^ a ≤ (N * t) ^ (k + 1 + a) := by
  have h0 : 0 ≤ N := by linarith
  have ht : 1 ≤ t := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : N ≤ N * t := le_mul_of_one_le_right h0 ht
  calc A * N * (N * (e + 1)) ^ a ≤ N ^ k * N * (N * t) ^ a := by gcongr
    _ ≤ (N * t) ^ k * (N * t) * (N * t) ^ a := by gcongr
    _ = (N * t) ^ (k + 1 + a) := by ring

theorem UpperTheory.V.U3.countI :
    CorGK → CountI := by
  intro hC χ
  classical
  obtain ⟨hpK, hpK4, hpK7, hpKcop⟩ := (pK_pOne_prime_conditions χ).1
  obtain ⟨hdisc, -, -, -⟩ := kstar (pK χ) hpK hpK4
  obtain ⟨c₅, A, hcor⟩ := hC (Kstar (pK χ))
  obtain ⟨r₁, hr₁B, hr₁⟩ := Nat.exists_infinite_primes (30 * χ.N * pK χ + 1)
  obtain ⟨r₂, hr₂B, hr₂⟩ := Nat.exists_infinite_primes (r₁ + 1)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) (by norm_num : (1 : ℝ) < 16)
  refine ⟨k + 1 + A, r₁, r₂, hr₁, hr₂, ?_⟩
  intro h hχ h1q h1d h2q h2d t hBig e he het Ω _ _ _ c Ls hLs
  subst hχ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra (Kstar (pK h.chi)) Ω :=
    (IsAlgClosed.lift (M := Ω) (R := ℚ) (S := Kstar (pK h.chi))).toRingHom.toAlgebra
  obtain ⟨-, -, h16, -, -, hprimeN, -⟩ := hostIndex h
  have hN0 := h.N_pos
  have hqpos : 0 < h.chi.N := Nat.pos_of_ne_zero (h.chi.ne.out)
  have hnd : ∀ p : ℕ, p.Prime → 30 * h.chi.N * pK h.chi + 1 ≤ p → p < h.q1 → p < h.d →
      ¬ p ∣ 30 * h.N * (NumberField.discr (Kstar (pK h.chi))).natAbs := by
    intro p hp hpB hpq hpd hdiv
    rw [hdisc, Int.natAbs_neg, Int.natAbs_natCast] at hdiv
    have hp30 : 30 < p := by nlinarith [hpK7]
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · rcases (hprimeN p hp).1 h2 with h3 | h3 | h3 | h3
        · omega
        · have := Nat.le_of_dvd hqpos h3
          nlinarith [hpK7]
        · omega
        · omega
    · have := Nat.le_of_dvd (by omega) h1
      nlinarith [hqpos]
  have hnd1 := hnd r₁ hr₁ hr₁B h1q h1d
  have hnd2 := hnd r₂ hr₂ (by omega) h2q h2d
  have hne : r₁ ≠ r₂ := by omega
  set T : Finset (Subgroup (ZMod h.N)ˣ) :=
    Ls.biUnion (fun l => (h.X (c l) e).image (fun ψ => (MulChar.toUnitHom ψ).ker)) with hT
  have hcorK : ∀ K' : Subgroup (ZMod h.N)ˣ,
      (∀ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        ∀ ψ ∈ orb (c l) K', Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
        Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ ≤
        2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := by
    intro K'
    refine hcor Ω e h.N K' r₁ r₂ hr₁ hr₂ hne hnd1 hnd2 c _ ?_
    intro l hl
    obtain ⟨hlLs, ψ, hψ, hker⟩ := Finset.mem_filter.1 hl
    obtain ⟨hchar, hpar⟩ := (Host.mem_X h).1 hψ
    exact ⟨ψ, (mem_orb _).2 hker, gdOfHost h t hBig Ω l e (hLs l hlLs).1 he het (hLs l hlLs).2 _ ψ hchar hpar⟩
  have hmapT : ∀ l ∈ Ls, ∀ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker ∈ T := by
    intro l hl ψ hψ
    rw [hT, Finset.mem_biUnion]
    exact ⟨l, hl, Finset.mem_image_of_mem _ hψ⟩
  have hsumT : ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) ≤ (h.N : ℝ) := by
    have hcyc : ∀ K' ∈ T, IsCyclic ((ZMod h.N)ˣ ⧸ K') := by
      intro K' hK'
      rw [hT, Finset.mem_biUnion] at hK'
      obtain ⟨l, -, hK'⟩ := hK'
      obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hK'
      exact (orbFacts _ h.N ψ).2.1
    have h1 := orbSum (ZMod h.N)ˣ T hcyc
    have h2 : Nat.card (ZMod h.N)ˣ ≤ h.N := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
      exact Nat.totient_le _
    exact_mod_cast h1.trans h2
  have hc5 : (0 : ℝ) ≤ c₅ := by positivity
  have hL : 0 ≤ Real.log r₁ + Real.log r₂ := add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hP : 0 ≤ ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by positivity
  have hN16 : (16 : ℝ) ≤ h.N := by exact_mod_cast Nat.le_of_dvd hN0 h16
  have het' : (e : ℝ) + 1 ≤ t := by exact_mod_cast Nat.succ_le_of_lt het
  refine ⟨?_, ?_⟩
  · intro l hl ψ hψ
    exact (hcorK _).1 l (Finset.mem_filter.2 ⟨hl, ψ, hψ, rfl⟩) ψ ((mem_orb _).2 rfl)
  · have hstep : ∀ l ∈ Ls, Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ h.X (c l) e, Vn Ω (c l) e ψ ≤
        ∑ K' ∈ T, if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0 := by
      intro l hl
      have hlog : 0 ≤ Real.log ((l : ℕ) : ℝ) := Real.log_natCast_nonneg _
      rw [← Finset.sum_fiberwise_of_maps_to (hmapT l hl), Finset.mul_sum]
      refine Finset.sum_le_sum fun K' _ => ?_
      split_ifs with hex
      · apply mul_le_mul_of_nonneg_left _ hlog
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro ψ hψ
          exact (mem_orb _).2 (Finset.mem_filter.1 hψ).2
        · intro ψ _ _
          exact Vn_nonneg Ω _ e ψ
      · have hempty : (h.X (c l) e).filter (fun ψ => (MulChar.toUnitHom ψ).ker = K') = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro ψ hψ hk
          exact hex ⟨ψ, hψ, hk⟩
        rw [hempty, Finset.sum_empty, mul_zero]
    calc _ ≤ ∑ l ∈ Ls, ∑ K' ∈ T, (if (∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K') then
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ else 0) := Finset.sum_le_sum hstep
      _ = ∑ K' ∈ T, ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, (MulChar.toUnitHom ψ).ker = K'),
          Real.log ((l : ℕ) : ℝ) * ∑ ψ ∈ orb (c l) K', Vn Ω (c l) e ψ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun K' _ => ?_
        rw [Finset.sum_filter]
      _ ≤ ∑ K' ∈ T, 2 * (c₅ : ℝ) * (K'.index.totient : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          (Real.log r₁ + Real.log r₂) := Finset.sum_le_sum fun K' _ => (hcorK K').2
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A *
          ∑ K' ∈ T, ((K'.index.totient : ℕ) : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun K' _ => by ring
      _ ≤ (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A * (h.N : ℝ) :=
        mul_le_mul_of_nonneg_left hsumT (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc5) hL) hP)
      _ = (2 * (c₅ : ℝ) * (Real.log r₁ + Real.log r₂)) * (h.N : ℝ) * ((h.N : ℝ) * ((e : ℝ) + 1)) ^ A := by ring
      _ ≤ ((h.N : ℝ) * (t : ℝ)) ^ (k + 1 + A) :=
        absorb _ _ _ _ k A hk.le hN16 (Nat.cast_nonneg e) het'
