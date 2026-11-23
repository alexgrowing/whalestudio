import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SpanUnif

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix

namespace UpperTheory.V.Sd.EG

section Loc
open GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w 2) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w 2) (KGL w 2) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2 := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

private theorem sat_two {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V}
    {x : V} {B : Multiset ℂˣ} (h : IsSatVecGL w ρ x B) : ∃ α β : ℂˣ, B = {α, β} ∧
      Uop w ρ 0 x = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • x ∧
      ρ (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = ((α * β : ℂˣ) : ℂ) • x := by
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 h.2.2.1
  refine ⟨α, β, rfl, ?_, ?_⟩
  · rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]),
      h.2.2.2 _ (unif_spec w) 1 (by norm_num)]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := rfl
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h.2.2.2 _ (unif_spec w) 2 le_rfl
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      (GlobalTheory.LGrp.mem_fixed.1 h.2.1), Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]

private theorem root {K : Type} [NormedField K] [IsUltrametricDist K] {u v q : K} (h : ‖v‖ ≤ ‖u‖) (h1 : ‖u + v - 1‖ < 1)
    (h2 : ‖u * v‖ < ‖q‖) (h3 : ‖q‖ ≤ 1) : ‖u - 1‖ < 1 ∧ v ≠ q * u := by
  have h4 : 1 ≤ ‖u‖ := by
    by_contra h5
    have h6 := IsUltrametricDist.norm_add_le_max (u + v) (-(u + v - 1))
    have h7 := IsUltrametricDist.norm_add_le_max u v
    rw [norm_neg, show u + v + -(u + v - 1) = 1 by ring, norm_one] at h6
    rw [max_eq_left h] at h7
    exact absurd h6 (not_le.2 (max_lt (h7.trans_lt (not_le.1 h5)) h1))
  have h5 : ‖v‖ < ‖q‖ := lt_of_le_of_lt (by rw [norm_mul]; exact le_mul_of_one_le_left (norm_nonneg _) h4) h2
  refine ⟨?_, fun e => ?_⟩
  · have h6 := IsUltrametricDist.norm_add_le_max (u + v - 1) (-v)
    rw [norm_neg, show u + v - 1 + -v = u - 1 by ring] at h6
    exact h6.trans_lt (max_lt h1 (h5.trans_le h3))
  · rw [e, norm_mul] at h5
    exact absurd (le_mul_of_one_le_right (norm_nonneg _) h4) (not_le.2 h5)

theorem stab [IsTotallyReal F] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : TR.CuspSub F 2) {B : Multiset ℂˣ} (hB : π.HasSat w B)
    {a d : ℂ} (e : ((algSat 2 (normV w) B).map fun b => X - C b).prod = X ^ 2 - C a * X + C d)
    (ha : ‖ι.symm a - 1‖ < 1) (hd : ‖ι.symm d‖ < ‖(normV w : Qbar l)‖) :
    ∃ lam, HasU w (π.locRep w) 1 lam ∧ ‖ι.symm lam - 1‖ < 1 := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB.1
  obtain ⟨α, β, rfl, h2, h3⟩ := sat_two w (hB.2 x hx hx0)
  set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
  have h9 : algSat 2 (normV w) {α, β} = {r * α, r * β} := by
    simp only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    norm_num
  have hrr : r * r = normV w := by
    rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add' (by positivity) (by norm_num)]
    norm_num
  rw [h9] at e
  have h0 := congrArg (eval 0) e
  have h1 := congrArg (eval 1) e
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C] at h0 h1
  have hs : r * α + r * β = a := by linear_combination h0 - h1
  have hp : r * α * (r * β) = d := by linear_combination h0
  have hx' : x ∈ Hi.fixd (π.locRep w) (K1 w 0) := by
    rw [iwahori_level_zero_eq]; exact GlobalTheory.LGrp.mem_fixed.1 hx
  have key : ∀ u v : ℂ, u + v = a → u * v = d → ‖ι.symm v‖ ≤ ‖ι.symm u‖ →
      ∃ lam, HasU w (π.locRep w) 1 lam ∧ ‖ι.symm lam - 1‖ < 1 := fun u v e1 e2 h => by
    obtain ⟨k1, k2⟩ := root h (by rwa [← map_add, e1]) (by rwa [← map_mul, e2]) (IsUltrametricDist.norm_natCast_le_one _ _)
    refine ⟨u, pStab F w _ _ x u v hx0 hx' (by rw [h2, e1, ← hs, mul_add]) ?_ fun e => k2 (by rw [e, map_mul, map_natCast]), k1⟩
    rw [h3, smul_smul, e2, ← hp, ← hrr, Units.val_mul]
    congr 1
    ring
  rcases le_total ‖ι.symm (r * β)‖ ‖ι.symm (r * α)‖ with h | h
  · exact key _ _ hs hp h
  · exact key _ _ ((add_comm _ _).trans hs) ((mul_comm _ _).trans hp) h

end Loc

theorem normV_eq (v : Pl ℚ) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem dvd_of_mem {I : Ideal (𝓞 ℚ)} {n : ℕ} (h : (n : 𝓞 ℚ) ∈ I) : Ideal.absNorm I ∣ n := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem I).2 h)
  rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one] at h1

theorem mem_iff (v : Pl ℚ) (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ n := by
  rw [normV_eq]
  refine ⟨dvd_of_mem, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem normV_prime (v : Pl ℚ) : (normV v).Prime := by
  have h1 : 1 < normV v := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine Nat.prime_def.2 ⟨h1, fun m hm => ?_⟩
  obtain ⟨c, hc⟩ := hm
  have h2 := (mem_iff v _).2 dvd_rfl
  rw [hc, Nat.cast_mul] at h2
  rcases v.isPrime.mem_or_mem h2 with h | h
  · exact Or.inr (Nat.dvd_antisymm ⟨c, hc⟩ ((mem_iff v _).1 h))
  · have h3 := Nat.dvd_antisymm (Dvd.intro_left m hc.symm) ((mem_iff v _).1 h)
    rw [h3] at hc
    exact Or.inl (Nat.eq_of_mul_eq_mul_right (by omega) (hc.symm.trans (one_mul _).symm))

theorem mem_iff_eq (v : Pl ℚ) {l : ℕ} (hl : l.Prime) : (l : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v = l := by
  rw [mem_iff, Nat.prime_dvd_prime_iff_eq (normV_prime v) hl]

theorem splitL {l : ℕ} (hl : l.Prime) : SplitL ℚ l := fun v hv => by
  have h := (normV_eq v).symm.trans ((mem_iff_eq v hl).1 hv)
  refine ⟨h, fun h2 => ?_⟩
  have h3 := dvd_of_mem h2
  rw [map_pow, h] at h3
  have h4 := Nat.le_of_dvd hl.pos h3
  have := hl.one_lt
  nlinarith

theorem fin_dvd {a : ℕ} (h : a ≠ 0) : {w : Pl ℚ | normV w ∣ a}.Finite := by
  have h0 : Ideal.span {(a : 𝓞 ℚ)} ≠ 0 := by simpa using h
  exact (Ideal.finite_factors h0).subset fun w hw => Ideal.dvd_span_singleton.2 ((mem_iff w a).2 hw)

end UpperTheory.V.Sd.EG
