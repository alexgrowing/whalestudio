import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open UpperTheory.V.Z.Kato.Joint

private theorem norm_le_of_pow {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (z : ℂ) (n : ℕ) (hn : n ≠ 0)
    (h : z ^ n = 1) : ‖ι.symm z‖ ≤ 1 := by
  have h1 : ‖ι.symm z‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1).le

private theorem hat_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    GlobalTheory.EisM.hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold GlobalTheory.EisM.hat
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) (fun _ _ => Finset.mem_univ _)
    (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y)) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun y _ => ZMod.natCast_zmod_val y) (fun i _ => ?_)
  have h : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
  rw [h, ZMod.stdAddChar_coe]
  push_cast
  rfl

private theorem norm_two' {l : ℕ} [hl : Fact l.Prime] (h : l ≠ 2) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h1 : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h1, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hl.out Nat.prime_two).mpr h)

theorem UpperTheory.V.Z.Kato.Joint.hatW :
    UpperTheory.V.Z.Kato.Joint.HatW := by
  intro l _ ι N _ θ hl
  refine ⟨?_, fun d => ?_, fun d => ?_⟩
  · by_contra hc
    push Not at hc
    have h0 : ZMod.dft (fun y : ZMod N => θ y) = 0 := by
      funext k
      have := hc (-k)
      rw [hat_std] at this
      rw [ZMod.dft_apply, Pi.zero_apply, ← this]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [mul_comm]
    have h1 := congrFun ((LinearEquiv.map_eq_zero_iff _).mp h0) 1
    simp at h1
  · have h2 : ι.symm 2 = 2 := map_ofNat _ 2
    rw [map_div₀, norm_div, h2, norm_two' hl, div_one, hat_std, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun y _ => ?_
    rw [map_mul, norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) ?_
    · by_cases hy : IsUnit y
      · obtain ⟨u, rfl⟩ := hy
        refine norm_le_of_pow ι _ (Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      · rw [MulChar.map_nonunit _ hy]; simp
    · refine norm_le_of_pow ι _ N (NeZero.ne N) ?_
      rw [← AddChar.map_nsmul_eq_pow]
      simp
  · rw [hat_std, hat_std]
    simp
