import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ExistsInfFilVEqBot

set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Ln34.CrystallineExponents

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [LocWach.Q, hs]

theorem cc_lev_pi (c : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    PowerSeries.constantCoeff (W.lev c ζ letπ) = ζ - 1 := by
  obtain ⟨E, hE0, -, hE⟩ := W.lev_π c ζ hζ
  have := congrArg PowerSeries.constantCoeff hE
  rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at this
  linear_combination this

theorem constantCoeff_q_zero_eq_p : PowerSeries.constantCoeff W.q₀ = (PD.p : O) := by
  have h := congrArg (PowerSeries.coeff 1) W.q₀_def
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
  rw [h, map_sub, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
  have e : ((1 : PowerSeries O) + PowerSeries.X) ^ PD.p =
      (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O) := by
    rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_one, add_comm]
  rw [e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]

theorem cc_lev_q_one (c : ZMod n) : PowerSeries.constantCoeff (W.lev c 1 W.q) = (PD.p : LL) := by
  have hq : W.q = (fun _ => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) W.q₀) * letπ +
      (PD.p : LetA O n) := by
    funext i
    simp only [LocWach.q, Pi.add_apply, Pi.mul_apply, letπ, Pi.natCast_apply]
    conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const W.q₀]
    rw [constantCoeff_q_zero_eq_p, map_natCast]
  rw [hq, map_add, map_mul, map_natCast, map_add, map_mul,
    cc_lev_pi W c 1 ⟨0, by rw [pow_zero]; exact IsPrimitiveRoot.one⟩, sub_self, mul_zero, zero_add,
    map_natCast]

theorem qroot_prim (hs : W.s = 1) (hp : (PD.p : LL) ≠ 0) {c : ZMod n} {ζ : LL}
    (h : Formalism.MainNotions.DeltaInvariantLattices.QRoot W c ζ) : IsPrimitiveRoot ζ PD.p := by
  obtain ⟨-, ⟨m, hm⟩, hcc⟩ := h
  rw [Q_eq_q W hs] at hcc
  have hpr : PD.p.Prime := PD.hp
  obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow hpr).1 (orderOf_dvd_of_pow_eq_one hm)
  have hprim : IsPrimitiveRoot ζ (PD.p ^ j) := hord ▸ IsPrimitiveRoot.orderOf ζ
  have hp1 : ζ ^ PD.p = 1 := by
    by_contra hne
    exact Formalism.MainNotions.UnusedSlot80.LevR.cc_lev_q W c ζ ⟨j, hprim⟩ hne hcc
  have hdvd : PD.p ^ j ∣ PD.p ^ 1 := by rw [pow_one]; exact hprim.dvd_of_pow_eq_one _ hp1
  have hj1 : j ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hpr.one_lt).1 hdvd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj1 with rfl | rfl
  · rw [pow_zero] at hprim
    obtain rfl := IsPrimitiveRoot.one_right_iff.1 hprim
    exact absurd (cc_lev_q_one W c ▸ hcc) hp
  · rwa [pow_one] at hprim

theorem letE_mul_self (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_smul_of_mem_Nl {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T}
    (hy : y ∈ W.Nl T c) : (letE c : LetA O n) • y = y := by
  obtain ⟨z, -, rfl⟩ := hy
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, letE_mul_self]

theorem Nl_le_N (T : LocLat G Qp LL O) (c : ZMod n) : W.Nl T c ≤ W.N T := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact (W.N T).smul_mem _ hz

theorem mem_Nl_of {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T} (hy : y ∈ W.N T)
    (hc : (letE c : LetA O n) • y = y) : y ∈ W.Nl T c :=
  ⟨y, hy, by simp only [LinearMap.smul_apply, LinearMap.id_apply]; exact hc⟩

theorem smul_eq_single {T : LocLat G Qp LL O} {c : ZMod n} {y : W.DD T}
    (hc : (letE c : LetA O n) • y = y) (o : O) :
    o • y = (Pi.single c (PowerSeries.C o) : LetA O n) • y := by
  conv_lhs => rw [← hc]
  rw [← smul_assoc]
  congr 1
  funext i
  by_cases h : i = c
  · subst h; simp [letE, PowerSeries.smul_eq_C_mul]
  · simp [letE, h]

theorem letπ_mul_single (c : ZMod n) (a : PowerSeries O) :
    (letπ : LetA O n) * Pi.single c a = Pi.single c (PowerSeries.X * a) := by
  funext i
  by_cases h : i = c
  · subst h; simp [letπ]
  · simp [letπ, h]

theorem levN_sum {T : LocLat G Qp LL O} (c : ZMod n) (ζ : LL) {r : ℕ} {b : Fin r → W.DD T}
    (hbN : ∀ m, b m ∈ W.N T) (a : Fin r → LetA O n) (hy : ∑ m, a m • b m ∈ W.N T) (j : ℤ) :
    W.levN T c ζ ⟨∑ m, a m • b m, hy⟩ j =
      ∑ m, smulS (W.lev c ζ (a m)) (W.levN T c ζ ⟨b m, hbN m⟩) j := by
  have e : (⟨∑ m, a m • b m, hy⟩ : ↥(W.N T)) = ∑ m, a m • (⟨b m, hbN m⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp [Submodule.coe_sum])
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [W.levN_smul]
  rfl

theorem rank_le (hFr : IsFractionRing O LL) (T : LocLat G Qp LL O) (c : ZMod n) {r : ℕ}
    {b : Fin r → W.DD T} (hbS : ∀ j, b j ∈ W.Nl T c)
    (hu : ∀ x ∈ W.Nl T c, ∃! a : Fin r → PowerSeries O,
      x = ∑ j, (Pi.single c (a j) : LetA O n) • b j)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)] :
    r ≤ finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) := by
  have hbN : ∀ m, b m ∈ W.N T := fun m => Nl_le_N W T c (hbS m)
  let bN : Fin r → ↥(W.N T) := fun m => ⟨b m, hbN m⟩
  have hcmp : ∀ m, W.cmp T (bN m) ∈ DcrisL PD T.ρ (W.emb c) := by
    intro m
    have e : (letE c : LetA O n) • bN m = bN m :=
      Subtype.ext (letE_smul_of_mem_Nl W (hbS m))
    rw [← e]
    exact W.cmp_letter T c (bN m)
  let vv : Fin r → ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) := fun m =>
    ⟨ιV PD (LL := LL) (V := T.V) (W.cmp T (bN m)), Submodule.mem_map_of_mem (hcmp m)⟩
  have hli : LinearIndependent LL vv := by
    refine Fintype.linearIndependent_iff.2 fun g hg m => ?_
    have hg' : ιV PD (LL := LL) (V := T.V) (∑ m, g m • W.cmp T (bN m)) = 0 := by
      have := congrArg Subtype.val hg
      simpa [vv, Submodule.coe_sum, map_sum, map_smul] using this
    have hsum : ∑ m, g m • W.cmp T (bN m) = 0 :=
      Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (PD := PD) (V := T.V) (hg'.trans (map_zero _).symm)
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
      (Finset.univ : Finset (Fin r)) g
    choose o ho using fun i => hint i (Finset.mem_univ i)
    haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
    have hdne : algebraMap O LL d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hcz : W.cmp T (∑ i, o i • bN i) = 0 := by
      rw [map_sum]
      simp only [W.cmp_smul]
      calc ∑ i, algebraMap O LL (o i) • W.cmp T (bN i)
          = ∑ i, algebraMap O LL d • (g i • W.cmp T (bN i)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ho i, Algebra.smul_def, mul_smul]
        _ = 0 := by rw [← Finset.smul_sum, hsum, smul_zero]
    obtain ⟨y, hy, hyz⟩ := h3.1 _ hcz
    set z : W.DD T := ∑ i, o i • b i with hz
    have hzc : ((∑ i, o i • bN i : ↥(W.N T)) : W.DD T) = z := by simp [hz, bN, Submodule.coe_sum]
    have hy' : (letπ : LetA O n) • y = z := by
      rw [← hzc, ← hyz]
      simp [Formalism.MainNotions.DeltaInvariantLattices.smulA]
    have hzl : z ∈ W.Nl T c := Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (hbS i)
    obtain ⟨a, ha, -⟩ := hu _ (mem_Nl_of W ((W.N T).smul_mem (letE c) hy) (by rw [smul_smul, letE_mul_self]))
    have rep1 : z = ∑ j, (Pi.single c (PowerSeries.C (o j)) : LetA O n) • b j := by
      rw [hz]
      exact Finset.sum_congr rfl fun j _ => smul_eq_single W (letE_smul_of_mem_Nl W (hbS j)) (o j)
    have rep2 : z = ∑ j, (Pi.single c (PowerSeries.X * a j) : LetA O n) • b j := by
      have e1 : z = (letE c : LetA O n) • z := (letE_smul_of_mem_Nl W hzl).symm
      rw [e1, ← hy', smul_comm, ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, letπ_mul_single]
    have heq := (hu z hzl).unique rep1 rep2
    have h0 : o m = 0 := by
      have := congrArg (fun f => PowerSeries.constantCoeff (f m)) heq
      simpa using this
    have : algebraMap O LL d * g m = 0 := by
      rw [← Algebra.smul_def, ← ho m, h0, map_zero]
    exact (mul_eq_zero.1 this).resolve_left hdne
  simpa using hli.fintype_card_le_finrank

theorem filC_anti (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) :
    Antitone (Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ) := fun a b hab =>
  sup_le_sup_right (inf_le_inf_left _ (filVB_anti PD hab)) _

theorem ddRE_inf_rest (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) :
    DdRE PD T.ρ τ ⊓ (⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ') = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun z hz => filV_sep PD (LL := LL) z fun a => ?_
  exact Formalism.MainNotions.UnusedSlot80.LevR.dR_sep T.ρ τ a
    ⟨(Submodule.mem_inf.1 hz).1, Submodule.mem_sup_right (Submodule.mem_inf.1 hz).2⟩

theorem mem_vanI_at (hFr : IsFractionRing O LL) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)
    (τ : K →ₐ[Qp] LL)
    (hfree : Formalism.MainNotions.DeltaInvariantLattices.FreeLetter W T (W.Nl T c) c) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (h41 : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ ((letE c : LetA O n) • x) k ∈
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊓ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k))
    (h42 : ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (a : LL), a ≠ 0 ∧
      (∀ j < k, a • W.levN T c ζ ((letE c : LetA O n) • x) j ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
      a • W.levN T c ζ ((letE c : LetA O n) • x) k - w ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1))
    [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)] [FiniteDimensional LL ↥(DdRE PD T.ρ τ)]
    (hdim : finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) ≤ finrank LL ↥(DdRE PD T.ρ τ))
    (y : W.DD T) (hy : y ∈ W.N T) (hyc : (letE c : LetA O n) • y = y) (k : ℕ)
    (hexp : ∀ j : ℤ, W.levN T c ζ ⟨y, hy⟩ j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - j)) :
    y ∈ Formalism.MainNotions.DeltaInvariantLattices.vanI W c ζ k • W.N T := by
  obtain ⟨r, b, hbS, hu⟩ := hfree
  have hbN : ∀ m, b m ∈ W.N T := fun m => Nl_le_N W T c (hbS m)
  have hCa := filC_anti (PD := PD) T τ
  have hFa : Antitone (FildR PD T.ρ τ) := fun a b hab => inf_le_inf_left _ (filVB_anti PD hab)
  obtain ⟨a₀, h₀⟩ := exists_le_filV PD (DdRE PD T.ρ τ)
  obtain ⟨a₁, h₁⟩ := exists_inf_filV_eq_bot PD (DdRE PD T.ρ τ)
  let e : Fin r → ℤ → T.V ⊗[Qp] BdR := fun m => W.levN T c ζ ⟨b m, hbN m⟩
  have hF : ∀ m k, e m k ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k) := fun m k => by
    have h := (Submodule.mem_inf.1 (h41 ⟨b m, hbN m⟩ k)).2
    rwa [Formalism.MainNotions.UnusedSlot80.LevR.levN_letE] at h
  have hLB : ∀ m, ∃ M, LB M (e m) := fun m => W.levN_supp T c ζ _
  have hexpand : ∀ (x : W.DD T) (hx : x ∈ W.N T), (letE c : LetA O n) • x = x →
      ∃ β : Fin r → PowerSeries O, x = ∑ m, (Pi.single c (β m) : LetA O n) • b m ∧
        ∀ j, W.levN T c ζ ⟨x, hx⟩ j =
          ∑ m, smulS (W.lev c ζ (Pi.single c (β m))) (e m) j := by
    intro x hx hxc
    obtain ⟨β, hβ, -⟩ := hu x (mem_Nl_of W hx hxc)
    refine ⟨β, hβ, fun j => ?_⟩
    have hs : ∑ m, (Pi.single c (β m) : LetA O n) • b m ∈ W.N T := hβ ▸ hx
    have e1 : (⟨x, hx⟩ : ↥(W.N T)) = ⟨_, hs⟩ := Subtype.ext hβ
    rw [e1]
    exact levN_sum W c ζ hbN _ hs j
  have hS : ∀ k : ℤ, ∀ w ∈ FildR PD T.ρ τ (-k),
      ∃ γ : Fin r → LL,
        (∀ j < k, ∑ m, γ m • e m j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
        ∑ m, γ m • e m k - w ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1) := by
    intro k w hw
    obtain ⟨x, α, hα, hlow, hk⟩ := h42 k w hw
    simp only [Formalism.MainNotions.UnusedSlot80.LevR.levN_letE] at hlow hk
    have hx'N : (letE c : LetA O n) • (x : W.DD T) ∈ W.N T := (W.N T).smul_mem _ x.2
    have hx'c : (letE c : LetA O n) • ((letE c : LetA O n) • (x : W.DD T)) =
        (letE c : LetA O n) • (x : W.DD T) := by rw [smul_smul, letE_mul_self]
    obtain ⟨β, -, hβ⟩ := hexpand _ hx'N hx'c
    have hxe : ∀ j, W.levN T c ζ x j =
        ∑ m, smulS (W.lev c ζ (Pi.single c (β m))) (e m) j := by
      intro j
      rw [← hβ j, ← Formalism.MainNotions.UnusedSlot80.LevR.levN_letE W T c ζ x j]
      rfl
    let γ : Fin r → LL := fun m => α * PowerSeries.constantCoeff (W.lev c ζ (Pi.single c (β m)))
    have key : ∀ j, α • W.levN T c ζ x j - ∑ m, γ m • e m j ∈
        Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1) := by
      intro j
      have e2 : α • W.levN T c ζ x j - ∑ m, γ m • e m j =
          ∑ m, α • (smulS (W.lev c ζ (Pi.single c (β m))) (e m) j -
            PowerSeries.constantCoeff (W.lev c ζ (Pi.single c (β m))) • e m j) := by
        rw [hxe j, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_sub, mul_smul]
      rw [e2]
      refine Submodule.sum_mem _ fun m _ => ?_
      obtain ⟨M, hM⟩ := hLB m
      exact Submodule.smul_mem _ _ (smulS_sub_cc hCa hM (hF m) _ j)
    refine ⟨γ, fun j hj => ?_, ?_⟩
    · have := Submodule.sub_mem _ (hlow j hj) (key j)
      rwa [sub_sub_cancel] at this
    · have := Submodule.sub_mem _ hk (key k)
      rwa [sub_sub_sub_cancel_left] at this
  have hr := (rank_le W hFr T c hbS hu h3).trans hdim
  obtain ⟨β, hβ, hyβ⟩ := hexpand y hy hyc
  have hdg : ∀ j : ℤ, ∑ m, smulS (W.lev c ζ (Pi.single c (β m))) (e m) j ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - j) := by
    intro j
    have := hexp j
    rwa [hyβ j] at this
  have hdvd := dvd_of_dg_mod hFa (DdRE PD T.ρ τ) _ (fun a => inf_le_left) (ddRE_inf_rest T τ)
    a₀ a₁ (le_inf le_rfl h₀) h₁ hLB hF hS hr k _ hdg
  rw [hβ]
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem_smul ?_ (hbN m)
  show W.lev c ζ (Pi.single c (β m)) ∈ Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k}
  exact Ideal.mem_span_singleton.2 (hdvd m)

theorem mem_N_of_exp (hFr : IsFractionRing O LL) (hs : W.s = 1) (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) {M h : ZMod n → ℕ}
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.wachFree W T) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n)
    (hpt : ∀ ζ : LL, IsPrimitiveRoot ζ PD.p → ∃ τ, Pt c ζ τ)
    [FiniteDimensional LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c)]
    (hfd : ∀ τ, FiniteDimensional LL ↥(DdRE PD T.ρ τ))
    (hdim : ∀ τ, finrank LL ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c) ≤ finrank LL ↥(DdRE PD T.ρ τ))
    (y : W.DD T) (hyc : (letE c : LetA O n) • y = y) (hk : ∃ k : ℕ, W.Q ^ k • y ∈ W.N T)
    (hexp : ∀ ζ τ, Pt c ζ τ → ∀ (k : ℕ) (hk : W.Q ^ k • y ∈ W.N T) (i : ℤ),
      W.levN T c ζ ⟨W.Q ^ k • y, hk⟩ i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ ((k : ℤ) - i)) :
    y ∈ W.N T := by
  have hp : (PD.p : LL) ≠ 0 := by
    intro h0
    have := W.v_l
    rw [h0, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  refine (h5.2.2 y hk).2 fun i ζ hQ k' hk' => ?_
  by_cases hic : i = c
  · subst hic
    obtain ⟨τ, hτ⟩ := hpt ζ (qroot_prim W hs hp hQ)
    have := hfd τ
    obtain ⟨-, h41, h42⟩ := h4.2 i ζ τ hτ
    exact mem_vanI_at W hFr T i ζ τ (h1.2 i) h3 h41 h42 (hdim τ) (W.Q ^ k' • y) hk'
      (by rw [smul_comm, hyc]) k' (hexp ζ τ hτ k' hk')
  · have hl : (letE c : LetA O n) ∈ Formalism.MainNotions.DeltaInvariantLattices.vanI W i ζ k' := by
      show W.lev i ζ (letE c) ∈ Ideal.span {(PowerSeries.X : PowerSeries LL) ^ k'}
      rw [W.lev_letter i ζ _ (by simp [letE, Pi.single_eq_of_ne hic])]
      exact Ideal.zero_mem _
    have e1 : W.Q ^ k' • y = (letE c : LetA O n) • (W.Q ^ k' • y) := by rw [smul_comm, hyc]
    rw [e1]
    exact Submodule.smul_mem_smul hl hk'

end Loc

end Formalism.MainNotions.N.Ln34.CrystallineExponents

end
