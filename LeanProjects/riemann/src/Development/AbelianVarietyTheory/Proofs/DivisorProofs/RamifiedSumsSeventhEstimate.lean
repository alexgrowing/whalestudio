import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.BigTop.Fun.RamSum

section Norms

variable {F : Type} [Field F] [NumberField F]

theorem isPrimePow_absNorm (v : HeightOneSpectrum (𝓞 F)) : IsPrimePow (Ideal.absNorm v.asIdeal) := by
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card _

theorem sum_log_absNorm_le (S : Finset (HeightOneSpectrum (𝓞 F))) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ v ∈ S, (n : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ S, Real.log (Ideal.absNorm v.asIdeal) ≤ Module.finrank ℚ F * Real.log n := by
  have h1 : ∏ v ∈ S, v.asIdeal ∣ Ideal.span {(n : 𝓞 F)} :=
    Finset.prod_dvd_of_coprime (fun v _ w _ hvw => (HeightOneSpectrum.isCoprime_of_ne v w hvw))
      fun v hv => Ideal.dvd_span_singleton.2 (h v hv)
  have h2 := map_dvd Ideal.absNorm h1
  rw [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h2
  have h3 := Nat.le_of_dvd (by positivity) h2
  have h4 : ∀ v ∈ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := fun v _ => by
    exact_mod_cast (isPrimePow_absNorm v).ne_zero
  rw [← Real.log_prod h4, ← Real.log_pow]
  refine Real.log_le_log (Finset.prod_pos fun v hv => lt_of_le_of_ne (Nat.cast_nonneg _) (h4 v hv).symm) ?_
  exact_mod_cast h3

end Norms

theorem leaves_of_sum {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) (C b : ℝ) (hL : 0 ≤ Real.log b) (h0 : O.sv0 ∈ O.S0) (hq : ∀ q ∈ O.S0, IsPrimePow (O.qq q))
    (hS : ∑ q ∈ O.S0, Real.log (O.qq q) ≤ 21 * (O.f * Real.log b)) (hc : ∀ q ∈ O.S0, O.cc q ≤ 2)
    (hP : 42 * (O.f * Real.log b) ≤ O.PPF C b) : PrimePowerModuliSumBound O C b ∧ LeafCS O b := by
  classical
  have hfL : 0 ≤ O.f * Real.log b := by positivity
  have hlq : 0 < Real.log (O.qq O.sv0) := Real.log_pos (by exact_mod_cast (hq _ h0).one_lt)
  have hP0 : 0 ≤ O.PPF C b := by linarith
  refine ⟨⟨hq, ?_⟩, ?_⟩
  · unfold FunData.Sig0
    rw [← Finset.add_sum_erase _ _ h0] at hS ⊢
    have e1 : ∑ q ∈ O.S0.erase O.sv0, (O.ee C b q : ℝ) * Real.log (O.qq q) =
        2 * ∑ q ∈ O.S0.erase O.sv0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq' => ?_
      simp [FunData.ee, Finset.ne_of_mem_erase hq']
    have e2 : (O.ee C b O.sv0 : ℝ) * Real.log (O.qq O.sv0) ≤ O.PPF C b + Real.log (O.qq O.sv0) := by
      have h := Nat.floor_le (div_nonneg hP0 hlq.le)
      rw [le_div_iff₀ hlq] at h
      simp only [FunData.ee, if_true]
      push_cast
      linarith
    rw [e1]
    linarith
  · unfold LeafCS FunData.cS
    have e1 : ∑ q ∈ O.S0, (O.cc q : ℝ) * Real.log (O.qq q) ≤ 2 * ∑ q ∈ O.S0, Real.log (O.qq q) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq' => mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg _)
      exact_mod_cast hc q hq'
    linarith

theorem ramifiedPlaces_sum_log_absNorm_le {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) (s : Formalism.BasicNotions.Scale)
    (hg : ∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * s.L)) (h1 : (D.host.pde : ℝ) < s.X')
    (h2 : (D.host.pde' : ℝ) < s.X') (h3 : ((GlobalTheory.ChiGrid.q0 D : ℕ) : ℝ) < s.X') :
    ∑ v ∈ P.S0, Real.log (Ideal.absNorm v.asIdeal) ≤ 21 * (D.R.f * Real.log s.b) := by
  have p0 := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have p1 := (D.host.g_prime 0).pos
  have p2 := (D.host.g_prime 1).pos
  have p3 := D.host.pde_prime.pos
  have p4 := D.host.pde'_prime.pos
  have hF : Module.finrank ℚ D.host.F = D.R.f := by
    rw [D.host.finrank_hostF, Ranks.f, Ranks.n]
  have key := sum_log_absNorm_le P.S0
    (n := GlobalTheory.ChiGrid.q0 D * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')) (by positivity) fun v hv => by
      rw [Nat.cast_mul]
      rcases P.mem_S0_of_sum_eq.1 hv with rfl | hv
      · exact Ideal.mul_mem_right _ _ P.basePlace_over_qZero
      · exact Ideal.mul_mem_left _ _ (Formalism.L2.DIV.mem_primesOf.1 hv).2
  rw [hF] at key
  refine key.trans ?_
  have hb : Real.log s.b = s.L := Real.log_exp _
  have hX : s.X' ≤ Real.exp s.L :=
    Real.exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith [s.eps_pos]))
  have hl : ∀ {n : ℕ} {y : ℝ}, 0 < n → (n : ℝ) ≤ Real.exp y → Real.log n ≤ y := fun hn h =>
    (Real.log_le_iff_le_exp (by exact_mod_cast hn)).2 h
  have a0 := hl p0 (h3.le.trans hX)
  have a1 := hl p1 (hg 0)
  have a2 := hl p2 (hg 1)
  have a3 := hl p3 (h1.le.trans hX)
  have a4 := hl p4 (h2.le.trans hX)
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), hb, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

theorem le_PPF {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}
    (O : FunData K Df) {C b : ℝ} (hC : 42 ≤ C) (hb : 1 ≤ b) (hf : 1 ≤ O.f) (hn : 1 ≤ O.nr) (h1 : 1 ≤ O.g1) (h2 : 1 ≤ O.g2)
    (h3 : 1 ≤ O.pd) (h4 : 1 ≤ O.pd') (h5 : O.dE ≠ 0) : 42 * (O.f * Real.log b) ≤ O.PPF C b := by
  have hf' : (1 : ℝ) ≤ O.f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ O.nr := by exact_mod_cast hn
  have h1' : (1 : ℝ) ≤ O.g1 := by exact_mod_cast h1
  have h2' : (1 : ℝ) ≤ O.g2 := by exact_mod_cast h2
  have h3' : (1 : ℝ) ≤ O.pd := by exact_mod_cast h3
  have h4' : (1 : ℝ) ≤ O.pd' := by exact_mod_cast h4
  have h5' : (1 : ℝ) ≤ |(O.dE : ℝ)| := by exact_mod_cast Int.one_le_abs h5
  have hl : 0 ≤ Real.log b := Real.log_nonneg hb
  have e1 : Real.log b ≤ Real.log (b * O.nr * O.g1 * O.g2 * O.pd * O.pd' * |(O.dE : ℝ)|) := by
    refine Real.log_le_log (by linarith) ?_
    calc b = b * 1 * 1 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have e2 : (O.f : ℝ) ≤ (O.f : ℝ) ^ 2 := le_self_pow₀ hf' two_ne_zero
  have e3 : (1 : ℝ) ≤ (O.nr : ℝ) ^ 6 := one_le_pow₀ hn'
  unfold FunData.PPF
  calc 42 * (O.f * Real.log b) = 42 * O.f * 1 * Real.log b := by ring
    _ ≤ _ := by gcongr

end GlobalTheory.BigTop.Fun.RamSum

namespace GlobalTheory.BigTop.Fun

open RamSum

theorem ramified_sums_seventh_bound : RamifiedSumBound := by
  refine ⟨0, fun CF _ => ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hF _ _ => ?_⟩⟩⟩
  refine ⟨42, fun C hC => EvPt.of_forall fun x hx i p _ d _ => ?_⟩
  obtain ⟨-, -, hg, h1, h2, -⟩ := hF.1.2.2.2.2.2.2.2.2 x hx i
  have h3 := hF.2.2.1 x hx i
  have hb : 1 ≤ (Fm.L x i).sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine leaves_of_sum d.O C p.Z.b (Real.log_nonneg hb) (d.G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)) (fun v _ => isPrimePow_absNorm v)
    (ramifiedPlaces_sum_log_absNorm_le d.G.pl (Fm.L x i).sc hg h1 h2 h3) (fun v _ => ?_)
    (le_PPF d.O hC hb ?_ ?_ ((Fm.D x i).host.g_prime 0).pos ((Fm.D x i).host.g_prime 1).pos (Fm.D x i).host.pde_prime.pos
      (Fm.D x i).host.pde'_prime.pos (discr_ne_zero _))
  · unfold FunIn.O FunIn.data
    dsimp only
    split_ifs <;> omega
  · have := (Fm.D x i).R.m_le_f
    have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.f
    unfold Ranks.f Ranks.n
    omega
  · have := (Fm.D x i).R.two_le_m
    show 1 ≤ (Fm.D x i).R.k + (Fm.D x i).R.m
    omega

end GlobalTheory.BigTop.Fun
