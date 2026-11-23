import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.LocCAsm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct

theorem locC_of_steps (hP : UnrPoly) (hCI : CosetInt) (hTE : TsumExhaust) (hNP : NuPow) (hNB : NuBound)
    (hLC : LevChars) (hVH : HermitianLatticeVolumeOne) (hJ : JtLev) (hNL : NuLev) (hPL : PsiLev) (hEx : Exhaust) (hCL : ClassLev)
    (hInv : HermitianLatticeInvariance) (hCM : CosetMeas) : LocC := by
  classical
  intro F E _ _ _ _ _ σ M n d J T hT bs v ψv S σS ϖ ε hG μv νv lam L hμ hν hlam hL z hz
  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hR : IsUnrQuad S σS hG.pS q ε := hG.quad
  have hq1 : 1 < q := hR.one_lt
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hfin : ∀ k, Finite (S ⧸ lev hG.pS k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card S σS hG.pS q ε hR k]; exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (S ⧸ lev hG.pS k) := fun k => Fintype.ofFinite _
  letI : ∀ k, Fintype (hermMod σS hG.pS n k) := fun k => Fintype.ofFinite _
  have hε1 : ‖(ε : ℂ)‖ = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

  set f := whI (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (nu2 lam L L) (hermOf (Fv F v) σ T hT).1 z with hf
  have hinv : ∀ b h, h ∈ H0 S σ n → f (b + h) = f b := fun b h hh =>
    hInv F E σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  let fbar : HermR (Fv F v) σ n ⧸ H0 S σ n → ℂ := fun c => f (Quotient.out c)
  have hfbar : ∀ g, f g = fbar (QuotientAddGroup.mk g) := by
    intro g
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) :
        HermR (Fv F v) σ n ⧸ H0 S σ n) = QuotientAddGroup.mk g := Quotient.out_eq' _
    rw [QuotientAddGroup.eq] at h1
    have := hinv (Quotient.out (QuotientAddGroup.mk g : HermR (Fv F v) σ n ⧸ H0 S σ n)) _ h1
    rw [add_neg_cancel_left] at this
    exact this

  set t : ℂ := (ε : ℂ) ^ M * (q : ℂ) ^ (-(2 * z + n)) with ht
  have hval : ∀ k (B : hermMod σS hG.pS n k), fbar (hG.iota k B) =
      t ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) *
        hG.psiLev (c := -1) (neg_mem (one_mem _)) k (Matrix.trace (red hG.pS k (matS S T hG.T_int) * B.1)) := by
    intro k B
    rw [GoodLoc.iota, ← hfbar]
    exact hG.f_lev hNP hJ hNL hPL hT μv hμ lam L hlam hL z k B

  let C : ℕ → Finset (HermR (Fv F v) σ n ⧸ H0 S σ n) := fun k => Finset.univ.image (hG.iota k)
  have hCmono : Monotone C := by
    refine monotone_nat_of_le_succ fun k => ?_
    intro c hc
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨B', hB'⟩ := hG.iota_succ hCL k B
    exact Finset.mem_image.2 ⟨B', Finset.mem_univ _, hB'⟩
  have hCcov : ∀ c, ∃ k, c ∈ C k := by
    intro c
    obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
    exact ⟨k, Finset.mem_image.2 ⟨B, Finset.mem_univ _, rfl⟩⟩
  have hsumC : ∀ k, ∑ c ∈ C k, fbar c = ∑ B : hermMod σS hG.pS n k, fbar (hG.iota k B) := fun k =>
    Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h
  have hnormC : ∀ k, ∑ c ∈ C k, ‖fbar c‖ = ∑ B : hermMod σS hG.pS n k, ‖t‖ ^ Nat.log (q ^ 2) (nuAt hG.pS B.1) := by
    intro k
    rw [Finset.sum_image fun B _ B' _ h => hG.iota_inj hCL k h]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, norm_mul, norm_pow, AddChar.norm_apply, mul_one]

  have htn : ‖t‖ = (q : ℝ) ^ (-(2 * z.re + n)) := by
    rw [ht, norm_mul, norm_pow, hε1, one_pow, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    simp
  have hlt : (q : ℝ) ^ (n ^ 2) * ‖t‖ < 1 := by
    rw [htn, ← Real.rpow_natCast, ← Real.rpow_add (by exact_mod_cast (by omega : 0 < q))]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq1)
    push_cast
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hbound : ∀ k, ∑ c ∈ C k, ‖fbar c‖ ≤ 1 / (1 - (q : ℝ) ^ (n ^ 2) * ‖t‖) := by
    intro k
    rw [hnormC]
    have := hNB S σS hG.pS q ε hR n k ‖t‖ (norm_nonneg _) hlt
    rwa [tsum_fintype] at this

  have hlc : IsLevelChars σS hG.pS (hG.psiLev (c := -1) (neg_mem (one_mem _))) :=
    hLC F E σ M n d J T bs v ψv S σS ϖ ε hG (-1) (neg_mem (one_mem _)) (by simp)
  have hpoly : ∀ k, 1 ≤ k → ∑ c ∈ C k, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    intro k hk
    rw [hsumC, ← hP S σS hG.pS q ε hR _ hlc n (matS S T hG.T_int) hG.T_unimod k hk t, tsum_fintype]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [hval, mul_comm]

  obtain ⟨hsum, htend⟩ := hTE _ fbar C hCmono hCcov ⟨_, hbound⟩
  have htsum : ∑' c, fbar c = ∏ i : Fin n, (1 - t * ((ε : ℂ) * q) ^ (i : ℕ)) := by
    refine tendsto_nhds_unique htend ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact (hpoly k hk).symm

  haveI := hν.1
  haveI := hCM F E σ M n d J T bs v ψv S σS ϖ ε hG |>.1
  have hcount : Countable (HermR (Fv F v) σ n ⧸ H0 S σ n) := by
    have : (Set.univ : Set (HermR (Fv F v) σ n ⧸ H0 S σ n)) ⊆ ⋃ k, Set.range (hG.iota k) := fun c _ => by
      obtain ⟨k, B, rfl⟩ := hG.iota_surj hCL hEx c
      exact Set.mem_iUnion.2 ⟨k, B, rfl⟩
    exact Set.countable_univ_iff.1 ((Set.countable_iUnion fun k => (Set.finite_range _).countable).mono this)
  obtain ⟨hI1, hI2⟩ := hCI _ νv (H0 S σ n) (hCM F E σ M n d J T bs v ψv S σS ϖ ε hG).2
    (hVH F E σ M n d J T bs v ψv S σS ϖ ε hG νv hν) hcount f fbar hfbar
  refine ⟨hI1.2 hsum, ?_⟩
  rw [hI2 hsum, htsum]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  rw [ht, mul_pow, mul_mul_mul_comm, ← pow_add, ← Complex.cpow_natCast (q : ℂ) (i : ℕ), ← Complex.cpow_add _ _ hq0]
  congr 2
  ring

end PositivityTheory.SiegelWeilFormula.Gunr

end
