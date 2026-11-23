import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlpBoundHolds

noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.AlTieEta

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.AlTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def TwoOver (𝔭 : Ideal (𝓞 D.host.F)) : Prop :=
  ∃ P Q : Ideal (𝓞 D.host.E), P ≠ Q ∧ P.IsPrime ∧ Q.IsPrime ∧
    P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭 ∧ Q.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭

theorem not_two_of_prime (𝔭 : Ideal (𝓞 D.host.F)) (h0 : 𝔭 ≠ ⊥)
    (hp : (𝔭.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime) : ¬ TwoOver 𝔭 := by
  rintro ⟨P, Q, hPQ, hP, hQ, hPc, hQc⟩
  have hI0 : 𝔭.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot h0
  have hmax : (𝔭.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsMaximal := hp.isMaximal hI0
  have hle : ∀ R : Ideal (𝓞 D.host.E), R.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = 𝔭 →
      𝔭.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ R :=
    fun R hR => Ideal.map_le_iff_le_comap.2 (le_of_eq hR.symm)
  have e1 := hmax.eq_of_le hP.ne_top (hle P hPc)
  have e2 := hmax.eq_of_le hQ.ne_top (hle Q hQc)
  exact hPQ (e1.symm.trans e2)

def sigO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)

theorem sigO_coe (x : 𝓞 D.host.E) : ((sigO x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E) := rfl

theorem sigO_alg (a : 𝓞 D.host.F) :
    sigO (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
  obtain ⟨-, hF, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  apply RingOfIntegers.ext
  rw [sigO_coe]
  exact (hF _).2 ⟨(a : D.host.F), rfl⟩

theorem prime_of_not_two (𝔭 : Ideal (𝓞 D.host.F)) [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) (hn : ¬ TwoOver 𝔭) :
    (𝔭.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
  obtain ⟨⟨-, -, hU⟩, -, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  have huniq : ∀ P Q : Ideal (𝓞 D.host.E), P ∈ 𝔭.primesOver (𝓞 D.host.E) → Q ∈ 𝔭.primesOver (𝓞 D.host.E) →
      P = Q := by
    intro P Q hP hQ
    by_contra hne
    exact hn ⟨P, Q, hne, hP.1, hQ.1, hP.2.over.symm, hQ.2.over.symm⟩
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) :=
    FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E)
  obtain ⟨P0, hP0max, hP0c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) 𝔭
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  have hP0 : P0 ∈ 𝔭.primesOver (𝓞 D.host.E) := ⟨hP0max.isPrime, ⟨hP0c.symm⟩⟩
  have : P0.IsPrime := hP0max.isPrime
  have : P0.LiesOver 𝔭 := ⟨hP0c.symm⟩
  have hfac := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 D.host.E) (S := 𝓞 D.host.F) (p := 𝔭) h0
  have hS : (𝔭.primesOver (𝓞 D.host.E)).toFinset = {P0} := by
    ext P
    rw [Set.mem_toFinset, Finset.mem_singleton]
    exact ⟨fun hP => huniq P P0 hP hP0, fun h => h ▸ hP0⟩
  rw [hS, Finset.prod_singleton] at hfac
  have hsum := Ideal.sum_ramification_inertia (𝓞 D.host.E) D.host.F D.host.E h0
  have hS' : IsDedekindDomain.primesOverFinset 𝔭 (𝓞 D.host.E) = {P0} := by
    ext P
    rw [Finset.mem_singleton, ← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset h0]
    exact ⟨fun hP => huniq P P0 hP hP0, fun h => h ▸ hP0⟩
  rw [hS', Finset.sum_singleton, Formalism.BasicNotions.Examples₂.finrank_FE D.host,
    Ideal.ramificationIdx'_eq_ramificationIdx 𝔭 P0 h0] at hsum
  have hf0 := Ideal.inertiaDeg'_pos 𝔭 P0
  have he1 : P0.ramificationIdx (𝓞 D.host.F) = 1 := by
    by_contra hne
    have he0 : P0.ramificationIdx (𝓞 D.host.F) ≠ 0 := by
      intro h; rw [h, zero_mul] at hsum; exact absurd hsum (by norm_num)
    have hf1 : 𝔭.inertiaDeg' P0 = 1 := by
      rcases Nat.lt_or_ge (𝔭.inertiaDeg' P0) 2 with h | h
      · omega
      · exfalso
        have : 2 * 2 ≤ P0.ramificationIdx (𝓞 D.host.F) * 𝔭.inertiaDeg' P0 :=
          Nat.mul_le_mul (by omega) h
        omega
    rw [Ideal.inertiaDeg_algebraMap] at hf1
    letI : Field (𝓞 D.host.F ⧸ 𝔭) := Ideal.Quotient.field 𝔭
    have hbt := Subalgebra.bot_eq_top_of_finrank_eq_one hf1
    obtain ⟨θ, t, ht, hθt⟩ := hU P0 hP0max
    have hts : t = sigO θ := RingOfIntegers.ext ht
    have hmem : Ideal.Quotient.mk P0 θ ∈ (⊥ : Subalgebra (𝓞 D.host.F ⧸ 𝔭) (𝓞 D.host.E ⧸ P0)) := by
      rw [hbt]; trivial
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hmem
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hc
    have h1 : θ - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P0 := by
      rw [← Ideal.Quotient.eq]; exact hc.symm
    have hσP : P0.map (sigO (D := D)) ∈ 𝔭.primesOver (𝓞 D.host.E) := by
      refine ⟨Ideal.map_isPrime_of_equiv _, ⟨?_⟩⟩
      show 𝔭 = (P0.map (sigO (D := D))).comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      ext x
      rw [Ideal.mem_comap, Ideal.mem_map_of_equiv]
      constructor
      · intro hx
        exact ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x, by rw [← Ideal.mem_comap, hP0c]; exact hx, sigO_alg x⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
          rw [← sigO_alg x] at hyx; exact sigO.injective hyx
        rw [← hP0c, Ideal.mem_comap, ← this]; exact hy
    have hσ := huniq _ _ hσP hP0
    have h2 : sigO θ - algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P0 := by
      rw [← hσ, ← sigO_alg a, ← map_sub]
      exact Ideal.mem_map_of_mem _ h1
    apply hθt
    rw [hts]
    have := P0.sub_mem h1 h2
    rwa [sub_sub_sub_cancel_right] at this
  rw [hfac, he1, pow_one]
  exact hP0max.isPrime

def LocGlobIdem : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)),
    IdemNT (v.adicCompletion F ⊗[F] E) ↔
      ∃ P Q : Ideal (𝓞 E), P ≠ Q ∧ P.IsPrime ∧ Q.IsPrime ∧
        P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ Q.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal

theorem twoOver_iff (p : PlF D) :
    TwoOver p.asIdeal ↔ ¬ (p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := by
  have : p.asIdeal.IsMaximal := p.isMaximal
  exact ⟨fun h hp => not_two_of_prime _ p.ne_bot hp h, fun h => by_contra fun hn => h (prime_of_not_two _ p.ne_bot hn)⟩

variable (X : HidaSetting D)

theorem etaV_eq_etaF (hLG : LocGlobIdem) (v : HeightOneSpectrum (𝓞 X.B.I.F)) :
    ((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ) =
      Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F (plEquiv X v).asIdeal := by
  have hjk : ∀ a : X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E a) =
      algebraMap D.host.F D.host.E (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X a) :=
    fun a => (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF_coe X a).symm
  have h1 := idemNT_iff (Formalism.L2.GlobalTheoryTheory.AFTransport.iotaF X) X.ιE hjk v
  have h2 := hLG D.host.F D.host.E (plEquiv X v)
  have hiff : IdemNT (v.adicCompletion X.B.I.F ⊗[X.B.I.F] X.B.I.E) ↔
      ¬ ((plEquiv X v).asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime :=
    (h1.trans h2).trans (twoOver_iff (plEquiv X v))
  unfold Formalism.L2.SG.LocVol.etaV Formalism.HermitianLattices.Ext.L3.etaF
  split_ifs with ha hb hb
  · exact absurd hb (hiff.1 ha)
  · simp
  · simp
  · exact absurd (hiff.2 hb) ha

def EtaF : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), ((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ) =
    Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F (plEquiv X v).asIdeal

def maxEquiv : HeightOneSpectrum (𝓞 X.B.I.F) ≃ {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} where
  toFun v := ⟨(plEquiv X v).asIdeal, (plEquiv X v).isMaximal⟩
  invFun 𝔭 := (plEquiv X).symm ⟨𝔭.1, 𝔭.2.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField 𝔭.2 (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  left_inv v := by
    show (plEquiv X).symm ⟨(plEquiv X v).asIdeal, _, _⟩ = v
    rw [Equiv.symm_apply_eq]
  right_inv 𝔭 := by
    apply Subtype.ext
    show ((plEquiv X) ((plEquiv X).symm _)).asIdeal = 𝔭.1
    rw [Equiv.apply_symm_apply]

variable {X} in

theorem summable_absNorm_inv (i : ℕ) (hi : 2 ≤ i) :
    Summable (fun p : PlF D => (((Ideal.absNorm p.asIdeal : ℕ) : ℝ))⁻¹ ^ i) := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, (Formalism.L2.SG.DataCut.qP p ^ i)⁻¹ ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ i)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f i hi
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable (fun p : PlF D => (Formalism.L2.SG.DataCut.qP p ^ i)⁻¹) :=
    summable_of_sum_le (fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)) hsum
  refine haS.congr fun p => ?_
  have hq : Formalism.L2.SG.DataCut.qP p = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := Formalism.L2.SG.Pf.LocModel.qPl_eq p
  rw [hq, inv_pow]

theorem euler_product_of_eta (hη : EtaF X) : Formalism.L2.SG.Pf.AlTieFD.EulerProductEta X := by
  intro i hi
  set x : HeightOneSpectrum (𝓞 X.B.I.F) → ℝ := fun v =>
    ((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i with hxdef
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F), (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    fun v => by exact_mod_cast Formalism.L2.SG.IntegralApproximation.absNorm_two_le v
  have hxabs : ∀ v, |x v| = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ i := by
    intro v
    have hη : |((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ)| = 1 := by
      unfold Formalism.L2.SG.LocVol.etaV; split_ifs <;> simp
    have hN0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith [hN2 v]
    rw [hxdef, abs_div, abs_pow, hη, one_pow, abs_pow, abs_of_pos hN0, inv_pow, one_div]
  have hxle : ∀ v, |x v| ≤ 1 / 4 := by
    intro v
    rw [hxabs v]
    have h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by linarith [hN2 v]) (by norm_num)]; linarith [hN2 v]
    have h0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := inv_nonneg.2 (by linarith [hN2 v])
    calc (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ i ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ 2 :=
          pow_le_pow_of_le_one h0 (by linarith) hi
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 1 / 4 := by norm_num
  have hy : ∀ v, 0 < 1 - x v := by
    intro v; have := hxle v; have := le_abs_self (x v); linarith
  have hpos : ∀ v, 0 < (1 - x v)⁻¹ := fun v => inv_pos.2 (hy v)
  have hlog : ∀ v, ‖Real.log ((1 - x v)⁻¹)‖ ≤ 2 * |x v| := by
    intro v
    have hx := hxle v
    rw [Real.log_inv, norm_neg, Real.norm_eq_abs, abs_le]
    have h1 := Real.log_le_sub_one_of_pos (hy v)
    have h2 := Real.one_sub_inv_le_log_of_pos (hy v)
    have h3 : -(2 * |x v|) ≤ 1 - (1 - x v)⁻¹ := by
      have e : 1 - (1 - x v)⁻¹ = -(x v) / (1 - x v) := by
        field_simp [(hy v).ne']
        ring
      rw [e, le_div_iff₀ (hy v)]
      rcases le_or_gt 0 (x v) with h | h
      · rw [abs_of_nonneg h] at hx ⊢; nlinarith
      · rw [abs_of_neg h] at hx ⊢; nlinarith
    have hxa := le_abs_self (x v)
    have hxb := neg_abs_le (x v)
    constructor <;> linarith
  have hsumx : Summable (fun v => |x v|) := by
    have h := (plEquiv X).summable_iff.2 (summable_absNorm_inv (D := D) i hi)
    refine h.congr fun v => ?_
    simp only [Function.comp, absNorm_plEquiv]
    rw [hxabs v]
  have hM : Multipliable (fun v => (1 - x v)⁻¹) :=
    Real.multipliable_of_summable_log hpos (Summable.of_norm_bounded (hsumx.mul_left 2) hlog)
  have hfg : (fun v => (1 - x v)⁻¹) = (fun 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} =>
      (1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ i * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(i : ℤ)))⁻¹) ∘ maxEquiv X := by
    funext v
    show _ = (1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F (plEquiv X v).asIdeal ^ i *
      (Ideal.absNorm (plEquiv X v).asIdeal : ℝ) ^ (-(i : ℤ)))⁻¹
    rw [hxdef]
    beta_reduce
    rw [← hη v, absNorm_plEquiv, zpow_neg, zpow_natCast, div_eq_mul_inv]
  show HasProd (fun v => (1 - x v)⁻¹) _
  rw [hfg] at hM ⊢
  unfold Formalism.HermitianLattices.Ext.L3.lValEtaF
  exact (maxEquiv X).hasProd_iff.2 ((maxEquiv X).multipliable_iff.1 hM).hasProd

theorem t_factor_product_of_eta (hη : EtaF X) (u : D.what₂.Word) : Formalism.L2.SG.Pf.AlTieFD.LocalFactorProduct X u := by
  set f : HeightOneSpectrum (𝓞 X.B.I.F) → ℝ := fun v => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((Formalism.L2.SG.LocVol.etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k
    else 1 with hfdef
  set h : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal} → ℝ := fun 𝔭 =>
    if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
      1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1
    with hhdef
  have hfin : Multipliable f := by
    apply multipliable_of_finite_mulSupport
    refine (Formalism.L2.SG.TypedSets.finite_over X.B.I.F ((D.mem u).A.T) (D.mem u).A.T_prime.ne_zero).subset ?_
    intro v hv
    by_contra hc
    exact (Function.mem_mulSupport.1 hv) (if_neg hc)
  have hfh : f = h ∘ maxEquiv X := by
    funext v
    show _ = if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (plEquiv X v).asIdeal then
      1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F (plEquiv X v).asIdeal ^ D.R.k *
        (Ideal.absNorm (plEquiv X v).asIdeal : ℝ) ^ (-(D.R.k : ℤ)) else 1
    rw [hfdef]
    beta_reduce
    rw [natCast_mem_plEquiv]
    split_ifs
    · rw [← hη v, absNorm_plEquiv, zpow_neg, zpow_natCast, div_eq_mul_inv]
    all_goals rfl
  show HasProd f (∏' 𝔭, h 𝔭)
  rw [hfh] at hfin ⊢
  exact (maxEquiv X).hasProd_iff.2 ((maxEquiv X).multipliable_iff.1 hfin).hasProd

theorem fieldDict_of_eta (hη : EtaF X) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' :=
  Formalism.L2.SG.Pf.AlTieFD.field_dictionary_of_leaves X u u' (euler_product_of_eta X hη) (t_factor_product_of_eta X hη u) Formalism.L2.SG.Pf.AlTieFD.discriminant_sq_relation

theorem fieldDict_of_locGlob (hLG : LocGlobIdem) (u u' : D.what₂.Word) : Formalism.L2.SG.Pf.NcVal.FieldDict X u u' :=
  fieldDict_of_eta X (fun v => etaV_eq_etaF X hLG v) u u'

end Formalism.L2.SG.Pf.AlTieEta
