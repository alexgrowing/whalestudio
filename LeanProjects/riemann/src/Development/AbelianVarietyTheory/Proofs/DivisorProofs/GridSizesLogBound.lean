import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelPrimeSplitsCompletelyInCmField

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.SqTop GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T}

theorem auxiliaryProduct_mem_place_of_exceptionalSet (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hp := v.isPrime
  simp only [Nat.cast_mul, hp.mul_mem_iff_mem_or_mem]
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h
  · exact Or.inr P.basePlace_over_qZero
  · rcases (S1_mem_OmF D).1 h with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)

theorem levQ_le (P : Places L) :
    levQ P ≤ ((D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D) ^ Module.finrank ℤ (𝓞 D.host.F)) ^ 2 := by
  classical
  set M := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' * q0 D with hM
  have hmem : ((M : ℕ) : 𝓞 D.host.F) ∈ ∏ v ∈ P.S0, v.asIdeal := by
    rw [← Ideal.dvd_span_singleton]
    exact Finset.prod_dvd_of_coprime (fun v _ w _ hne => HeightOneSpectrum.isCoprime_of_ne v w hne)
      fun v hv => Ideal.dvd_span_singleton.2 (auxiliaryProduct_mem_place_of_exceptionalSet P hv)
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  rw [Ideal.absNorm_span_natCast, map_prod] at hdvd
  have hM0 : 0 < M := by
    have := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    have := (D.host.g_prime 0).pos
    have := (D.host.g_prime 1).pos
    have := D.host.pde_prime.pos
    have := D.host.pde'_prime.pos
    positivity
  have hle := Nat.le_of_dvd (pow_pos hM0 _) hdvd
  calc levQ P = ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ condExp P v := rfl
    _ ≤ ∏ v ∈ P.S0, Ideal.absNorm v.asIdeal ^ 2 := by
      refine Finset.prod_le_prod' fun v _ => Nat.pow_le_pow_right ?_ ?_
      · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
      · unfold condExp; split_ifs <;> norm_num
    _ = (∏ v ∈ P.S0, Ideal.absNorm v.asIdeal) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ _ := Nat.pow_le_pow_left hle 2

theorem kap_add_le (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (i j : Fin D.R.m) {s : ℕ}
    (hs : s ≤ halfRank D i j) (τ : D.what₂.Tau) : (kap D 1 i j s τ : ℝ) + s ≤ 5 * large₂.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hhc, -⟩ := h
  have e := (Model.kap_add D 1 i j τ hs).1
  have e' := congrArg (Int.cast : ℤ → ℝ) e
  push_cast at e'
  rw [e']

  have he : (((num D 1 τ).e (j + 1) : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    have s1 := ((GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 j)
    have s2 : (((D.hc τ).e j : ℚ) : ℝ) = (((num D 1 τ).e (j + 1) : ℤ) : ℝ) := by
      rw [s1]; push_cast; rfl
    rw [← s2]; exact (hhc τ j).2

  set G0 := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have hv0 : 0 < D.R.k - 1 := by omega
  have hv : (G0.v 2 : ℚ) ≤ large₂.Sc := by
    have s1 := (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, hv0⟩
    have := (large₂.cloud_v τ ⟨0, hv0⟩).2
    rw [s1] at this
    exact_mod_cast this
  have hmid : ((G0.mid (D.R.m - i) : ℚ) : ℝ) ≤ large₂.Sc + ((D.R.m : ℝ) + 1) * gap D 1 + 1 / 2 := by
    have hi := i.2
    have hm : G0.m = D.R.m := rfl
    have hg : G0.ga = gap D 1 := rfl
    simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a, hm, hg]
    have hg0 : (0 : ℝ) ≤ gap D 1 := by positivity
    have hi' : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast hi
    have hv' : ((G0.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    have c1 : ((D.R.m - (i : ℕ) - 1 : ℕ) : ℝ) = D.R.m - (i : ℕ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have c2 : ((D.R.m - (i : ℕ) : ℕ) : ℝ) = D.R.m - (i : ℕ) := by
      rw [Nat.cast_sub (by omega)]
    push_cast
    rw [c1, c2]
    have hv'' : ((G0.v 2 : ℤ) : ℝ) ≤ large₂.Sc := by exact_mod_cast hv
    nlinarith [mul_le_mul_of_nonneg_right hi' hg0]
  have hc : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ large₂.sc.b := by
    have h1 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℚ) ≤ G0.mid (D.R.m - i) := Int.floor_le _
    have h2 : ((cen D 1 τ (D.R.m - i) : ℤ) : ℝ) ≤ ((G0.mid (D.R.m - i) : ℚ) : ℝ) := by exact_mod_cast h1
    linarith
  linarith

end GlobalTheory.SqTop.SizesBound

namespace GlobalTheory.SqTop.SizesBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sizes (c : ℝ) : GBig fun {D} _ _ {sc} G _ C x b => ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
    c * (Module.finrank ℚ D.host.E : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((kap D sc.cGap i j s τ : ℝ) + s)) ≤ bTH D C x b := by
  refine ⟨0, fun ε CF _ => ⟨2 * |c| + 100, 3, fun C hC D large₂ _ hx hR T Lc μ₀ _ G i j s _ hs => ?_⟩⟩
  have hS := hR.size
  obtain ⟨-, hSA, -, -, -, -, -, hgL, hqL, hrd, hcd, -, -, -⟩ := hR.size
  have hpde : Real.log (D.host.pde : ℝ) ≤ large₂.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ large₂.sc.L :=
    hSA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

  have hx1 : 1 < large₂.sc.x := by linarith
  have hLpos : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith) _
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp hLpos.le
  have hlx : 1 ≤ Real.log large₂.sc.x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _

  have h1 : c * (Module.finrank ℚ D.host.E : ℝ) ≤ 2 * |c| * D.R.f := by
    rw [Formalism.L2.Pj.hostSize_finrank D]; push_cast
    nlinarith [le_abs_self c]

  have h2 : Real.log |((discr D.host.E : ℤ) : ℝ)| ≤ 2 * D.R.f * large₂.sc.L := by
    have e : Real.log |((discr D.host.E : ℤ) : ℝ)| = logdE D := rfl
    rw [e, Formalism.BasicNotions.logdE_eq_rd]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    nlinarith

  have h3 : Real.log (levQ G.pl) ≤ 2 * D.R.f * (21 * large₂.sc.L + 2) := by
    have hle := levQ_le G.pl
    rw [NumberField.RingOfIntegers.rank, GlobalTheory.ColClassCompare.finrank_F] at hle
    have hpos : 0 < levQ G.pl := Finset.prod_pos fun v _ =>
      pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
    have hle' : (levQ G.pl : ℝ) ≤ ((((D.host.g 0 : ℕ) : ℝ) * (D.host.g 1 : ℕ) * (D.host.pde : ℕ) * (D.host.pde' : ℕ) *
        (q0 D : ℕ)) ^ D.R.f) ^ 2 := by exact_mod_cast hle
    have hl := Real.log_le_log (by exact_mod_cast hpos) hle'
    have p0 := (D.host.g_prime 0).pos
    have p1 := (D.host.g_prime 1).pos
    have p2 := D.host.pde_prime.pos
    have p3 := D.host.pde'_prime.pos
    have p4 := (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
    push_cast at hl
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)] at hl
    have g0 := hgL 0
    have g1 := hgL 1
    push_cast at hl
    nlinarith

  have h4 : ∑ τ, Real.log (1 + ((kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s τ : ℝ) + s)) ≤
      D.R.f * (5 + large₂.sc.L) := by
    have hk : ∀ τ, Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ 5 + large₂.sc.L := by
      intro τ
      have k1 := kap_add_le large₂ hS i j hs τ
      have k0 : (0 : ℝ) ≤ (kap D 1 i j s τ : ℝ) + s := by positivity
      calc Real.log (1 + ((kap D 1 i j s τ : ℝ) + s)) ≤ Real.log (6 * large₂.sc.b) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 6 + large₂.sc.L := by rw [Real.log_mul (by norm_num) (by linarith), hlogb]
        _ ≤ 5 + large₂.sc.L := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 by norm_num)
          linarith
    calc _ ≤ ∑ _τ : D.what₂.Tau, (5 + large₂.sc.L) := Finset.sum_le_sum fun τ _ => hk τ
      _ = D.R.f * (5 + large₂.sc.L) := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]

  show _ ≤ C * D.R.f * large₂.sc.b * (Real.log large₂.sc.b + Real.log large₂.sc.x)
  rw [hlogb]
  have hC0 : 0 ≤ C := by have := abs_nonneg c; linarith
  have t1 : (2 * |c| + 100) * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.L + 1) := by
    have : 0 ≤ (D.R.f : ℝ) * (large₂.sc.L + 1) := by positivity
    nlinarith
  have t2 : large₂.sc.L + 1 ≤ large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x) := by nlinarith
  have t3 : C * D.R.f * (large₂.sc.L + 1) ≤ C * D.R.f * (large₂.sc.b * (large₂.sc.L + Real.log large₂.sc.x)) :=
    mul_le_mul_of_nonneg_left t2 (by positivity)
  have t4 : 0 ≤ (D.R.f : ℝ) * large₂.sc.L := by positivity
  have t5 : 0 ≤ |c| * D.R.f := by positivity
  nlinarith

end GlobalTheory.SqTop.SizesBound

end
