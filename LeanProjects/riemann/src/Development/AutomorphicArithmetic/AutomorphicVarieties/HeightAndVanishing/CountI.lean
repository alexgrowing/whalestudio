import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.GdOfHost
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrbSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.primesex

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem absorb (A N t e : ℝ) (k : ℕ) (hA : 0 ≤ A) (hk : A ≤ 16 ^ k) (hN : 16 ≤ N) (he : 0 ≤ e) (het : e ≤ t)
    (ht : 1 ≤ t) : A * N * N ^ 18 * e ^ 7 ≤ (N * t) ^ (k + 19) := by
  have h0 : 0 ≤ N := by linarith
  have h1 : A ≤ N ^ k := hk.trans (pow_le_pow_left₀ (by norm_num) hN k)
  have h2 : e ^ 7 ≤ t ^ (k + 19) := (pow_le_pow_left₀ he het 7).trans (pow_le_pow_right₀ ht (by omega))
  calc A * N * N ^ 18 * e ^ 7 ≤ N ^ k * N * N ^ 18 * t ^ (k + 19) := by gcongr
    _ = (N * t) ^ (k + 19) := by ring

theorem UpperTheory.V.HV.countI :
    CorG → CountI := by
  classical
  rintro ⟨c5, hG⟩ χ
  obtain ⟨⟨hp, hp4, -, -⟩, -⟩ := pK_pOne_prime_conditions χ
  obtain ⟨hdisc, -, -, -⟩ := kstar (pK χ) hp hp4
  have hd : (discr (Kstar (pK χ))).natAbs = pK χ := by rw [hdisc]; simp
  have hq : 0 < χ.N := NeZero.pos _
  obtain ⟨r₁, hr₁, hr₁p⟩ := Nat.exists_infinite_primes (30 + χ.N + pK χ)
  obtain ⟨r₂, hr₂, hr₂p⟩ := Nat.exists_infinite_primes (r₁ + 1)
  set A : ℝ := 4 * |c5| * (pK χ : ℝ) ^ 5 * (Real.log r₁ + Real.log r₂) with hAdef
  have hlog : 0 ≤ Real.log r₁ + Real.log r₂ := add_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hA : 0 ≤ A := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt A (by norm_num : (1 : ℝ) < 16)
  refine ⟨k + 19, r₁, r₂, hr₁p, hr₂p, ?_⟩
  rintro h rfl a1 a2 a3 a4 t hB e he het Ω _ _ _ c Ls hLs
  obtain ⟨-, -, h16, -, -, hpr, -⟩ := hostIndex h
  have hnd : ∀ r : ℕ, r.Prime → 30 + h.chi.N + pK h.chi ≤ r → r < h.q1 → r < h.d →
      ¬ r ∣ 30 * h.N * (discr (Kstar (pK h.chi))).natAbs := by
    intro r hr b1 b2 b3 hdv
    rw [hd] at hdv
    rcases (Nat.Prime.dvd_mul hr).1 hdv with hdv | hdv
    · rcases (Nat.Prime.dvd_mul hr).1 hdv with hdv | hdv
      · have := Nat.le_of_dvd (by norm_num) hdv
        omega
      · rcases (hpr r hr).1 hdv with b | b | b | b
        · omega
        · have : r ≤ h.chi.N := Nat.le_of_dvd hq b
          omega
        · omega
        · omega
    · have := Nat.le_of_dvd hp.pos hdv
      omega
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  letI : Algebra (Kstar (pK h.chi)) Ω := (IsAlgClosed.lift (R := ℚ) (S := Kstar (pK h.chi)) (M := Ω)).toRingHom.toAlgebra
  have key := fun H : Subgroup (ZMod h.N)ˣ => hG Ω (Kstar (pK h.chi)) e h.N H r₁ r₂ hr₁p hr₂p (by omega)
    (hnd r₁ hr₁p hr₁ a1 a2) (hnd r₂ hr₂p (by omega) a3 a4) c
    (Ls.filter fun l => ∃ ψ ∈ h.X (c l) e, ψ.toUnitHom.ker = H) (by
      intro l hl
      obtain ⟨hl, ψ, hψ, hH⟩ := Finset.mem_filter.1 hl
      have := Host.mem_X h |>.1 hψ
      exact ⟨ψ, (mem_orb _).2 hH, gdOfHost h t hB Ω l e (hLs l hl).1 he het (hLs l hl).2 _ ψ this.1 this.2⟩)
  refine ⟨fun l hl ψ hψ => (key ψ.toUnitHom.ker).1 l (Finset.mem_filter.2 ⟨hl, ψ, hψ, rfl⟩) ψ ((mem_orb _).2 rfl), ?_⟩
  set T : Finset (Subgroup (ZMod h.N)ˣ) := Ls.biUnion fun l => (h.X (c l) e).image fun ψ => ψ.toUnitHom.ker with hT
  have hcyc : ∀ H ∈ T, IsCyclic ((ZMod h.N)ˣ ⧸ H) := by
    intro H hH
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.1 hH
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hl
    exact (orbFacts _ h.N ψ).2.1
  have hsum : ∑ H ∈ T, (Nat.totient H.index : ℝ) ≤ h.N := by
    have h1 := orbSum _ T hcyc
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h1
    exact_mod_cast h1.trans (Nat.totient_le _)
  have hN : (16 : ℝ) ≤ h.N := by exact_mod_cast Nat.le_of_dvd h.N_pos h16
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ h.X (c l) e, Vn Ω (c l) e ψ
      = ∑ l ∈ Ls, ∑ H ∈ T, Real.log (l : ℕ) * ∑ ψ ∈ (h.X (c l) e).filter (fun ψ => ψ.toUnitHom.ker = H), Vn Ω (c l) e ψ := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [← Finset.mul_sum]
        congr 1
        convert (Finset.sum_fiberwise_of_maps_to (s := h.X (c l) e) (t := T) (g := fun ψ => ψ.toUnitHom.ker)
          (fun ψ hψ => Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_image.2 ⟨ψ, hψ, rfl⟩⟩) (fun ψ => Vn Ω (c l) e ψ)).symm
    _ ≤ ∑ H ∈ T, ∑ l ∈ Ls.filter (fun l => ∃ ψ ∈ h.X (c l) e, ψ.toUnitHom.ker = H),
          Real.log (l : ℕ) * ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ := by
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun H _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs with hc
        · refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg _)
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun ψ hψ => (mem_orb _).2 (Finset.mem_filter.1 hψ).2)
            fun ψ _ _ => Vn_nonneg _ _ _ _
        · rw [Finset.filter_false_of_mem fun ψ hψ hk => hc ⟨ψ, hψ, hk⟩]
          simp
    _ ≤ ∑ H ∈ T, A * (Nat.totient H.index : ℝ) * (h.N : ℝ) ^ 18 * (e : ℝ) ^ 7 := by
        refine Finset.sum_le_sum fun H _ => (key H).2.trans ?_
        rw [hd, hAdef]
        calc _ ≤ 4 * |c5| * (Nat.totient H.index) * (pK h.chi : ℝ) ^ 5 * (h.N : ℝ) ^ 18 * (e : ℝ) ^ 7 *
              (Real.log r₁ + Real.log r₂) := by gcongr; exact le_abs_self _
          _ = _ := by ring
    _ = A * (∑ H ∈ T, (Nat.totient H.index : ℝ)) * (h.N : ℝ) ^ 18 * (e : ℝ) ^ 7 := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    _ ≤ A * h.N * (h.N : ℝ) ^ 18 * (e : ℝ) ^ 7 := by gcongr
    _ ≤ _ := absorb A h.N t e k hA hk.le hN (Nat.cast_nonneg _) (by exact_mod_cast het.le)
        (by exact_mod_cast (by omega : 1 ≤ t))
