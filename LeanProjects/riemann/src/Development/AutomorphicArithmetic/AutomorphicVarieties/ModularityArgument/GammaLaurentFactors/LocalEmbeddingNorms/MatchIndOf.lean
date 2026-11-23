import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExistsPullback
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.Regroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

namespace InductionMatchingPlacesAbove

section Primes

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem natCast_mem {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {q : ℕ}
    (hq : q.Prime) (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : 𝓞 F) ∈ w.asIdeal := by
  have hne : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hcard : Ideal.absNorm w.asIdeal = Nat.card (𝓞 F ⧸ w.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  have := Fact.mk hq
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 F ⧸ w.asIdeal) q (hcard ▸ hd)
  have h1 : q • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have := w.isPrime
  rw [nsmul_eq_mul] at h1
  have h2 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

private theorem normV_absNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private theorem absNorm_pow (w : HeightOneSpectrum (𝓞 M)) :
    Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.absNorm_pow_inertiaDeg]

private theorem sum_ef (hE : Module.finrank K M = 2) (v : HeightOneSpectrum (𝓞 K)) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 M), v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P = 2 := by
  have := v.isMaximal
  rw [← hE]
  exact Ideal.sum_ramification_inertia (𝓞 M) K M v.ne_bot

private theorem mem_over (w : HeightOneSpectrum (𝓞 M)) :
    w.asIdeal ∈ IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
  rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot]
  exact ⟨w.isPrime, ⟨rfl⟩⟩

private theorem e_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  exact Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (w.under (𝓞 K)).ne_bot)

private theorem f_pos (w : HeightOneSpectrum (𝓞 M)) : 0 < (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := (w.under (𝓞 K)).isMaximal
  exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ _)

private theorem f_one (hE : Module.finrank K M = 2) {w w' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w)
    (hu : w'.under (𝓞 K) = w.under (𝓞 K)) : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 1 := by
  classical
  have h1 := mem_over (K := K) w
  have h2 := mem_over (K := K) w'
  rw [hu] at h2
  have hne' : w.asIdeal ≠ w'.asIdeal := fun h => hne (HeightOneSpectrum.ext h.symm)
  have hsub : ({w.asIdeal, w'.asIdeal} : Finset (Ideal (𝓞 M))) ⊆
      IsDedekindDomain.primesOverFinset (w.under (𝓞 K)).asIdeal (𝓞 M) := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset
    (f := fun P => (w.under (𝓞 K)).asIdeal.ramificationIdx' P * (w.under (𝓞 K)).asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', sum_ef hE] at hle
  have a := e_pos (K := K) w
  have b := f_pos (K := K) w
  have c := e_pos (K := K) w'
  have d := f_pos (K := K) w'
  rw [hu] at c d
  have : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal ≤ 1 := by nlinarith
  omega

private theorem f_two (hE : Module.finrank K M = 2) (w : HeightOneSpectrum (𝓞 M))
    (honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w)
    (he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1) :
    (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 2 := by
  classical
  have h := sum_ef (K := K) (M := M) hE (w.under (𝓞 K))
  rw [Finset.sum_eq_single_of_mem w.asIdeal (mem_over w) (fun Q hQ hQw => ?_), he, one_mul] at h
  · exact h
  · exfalso
    apply hQw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (w.under (𝓞 K)).ne_bot] at hQ
    obtain ⟨hQp, hQl⟩ := hQ
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      apply (w.under (𝓞 K)).ne_bot
      rw [hQl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
    have := honly ⟨Q, hQp, hQ0⟩ (HeightOneSpectrum.ext hQl.over.symm)
    exact congrArg HeightOneSpectrum.asIdeal this

private theorem unram_bound (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    ∃ N : ℕ, ∀ w : HeightOneSpectrum (𝓞 M),
    ((N.factorial : ℕ) : 𝓞 K) ∉ (w.under (𝓞 K)).asIdeal → (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  obtain ⟨N, hN⟩ := ReciprocityTheory.Cheb.exists_forall_isUnramifiedAt M
  refine ⟨N, fun w hw => ?_⟩
  have h1 : 1 < Ideal.absNorm (w.under (𝓞 K)).asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm _
  have hq := Nat.minFac_prime h1.ne'
  have hqv : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ (w.under (𝓞 K)).asIdeal :=
    natCast_mem _ hq (Nat.minFac_dvd _)
  have hqN : N < Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) := by
    by_contra hle
    push_neg at hle
    apply hw
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hq.pos hle
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hqv
  have hqw : ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 M) ∈ w.asIdeal := by
    have : algebraMap (𝓞 K) (𝓞 M) ((Nat.minFac (Ideal.absNorm (w.under (𝓞 K)).asIdeal) : ℕ) : 𝓞 K) ∈ w.asIdeal := hqv
    rwa [map_natCast] at this
  haveI := w.isPrime
  haveI := hN _ hq hqN w.asIdeal hqw
  have hsq := ReciprocityTheory.Cheb.natCast_notMem_sq_of_isUnramifiedAt hq w.asIdeal
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one, Ideal.map_le_iff_le_comap]
    exact le_rfl
  · intro h
    have h3 := h (Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 M)) hqv)
    rw [map_natCast] at h3
    exact hsq (by simpa using h3)

private theorem exists_over (p : HeightOneSpectrum (𝓞 K)) :
    ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = p := by
  have := p.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) p.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply p.ne_bot
    rw [hQl.over]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨Q, hQm.isPrime, hQ0⟩, HeightOneSpectrum.ext hQl.over.symm⟩

private theorem finite_above (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S}.Finite := by
  classical
  have : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 K) ∈ S} ⊆
      ⋃ p ∈ S, HeightOneSpectrum.asIdeal ⁻¹' (↑(IsDedekindDomain.primesOverFinset (p : HeightOneSpectrum (𝓞 K)).asIdeal (𝓞 M)) : Set (Ideal (𝓞 M))) := by
    intro w hw
    exact Set.mem_biUnion hw (mem_over w)
  refine (hS.biUnion fun p _ => ?_).subset this
  exact (Finset.finite_toSet _).preimage (fun a _ b _ h => HeightOneSpectrum.ext h)

private theorem ind_key (hE : Module.finrank K M = 2) (sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop)
    (satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop) (hI : IndSys sat satP) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S →
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧
        w'.under (𝓞 K) = w.under (𝓞 K) ∧ ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 K)) (B + B')) ∨
      (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧
        ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧ B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 K)) B) := by
  classical
  obtain ⟨N, hN⟩ := unram_bound K M
  have hT := Filter.eventually_cofinite.1 hI
  have hR : {p : HeightOneSpectrum (𝓞 K) | ((N.factorial : ℕ) : 𝓞 K) ∈ p.asIdeal}.Finite := by
    have h0 : Ideal.span {((N.factorial : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.factorial_pos N).ne'
    exact (Ideal.finite_factors h0).subset fun p hp => Ideal.dvd_span_singleton.2 hp
  have hF := hR.union (hT.image fun w => w.under (𝓞 K))
  refine ⟨hF.toFinset, fun w hw => ?_⟩
  rw [Set.Finite.mem_toFinset] at hw
  have hgood := not_not.1 fun h => hw (Or.inr ⟨w, h, rfl⟩)
  have he := hN w fun h => hw (Or.inl h)
  by_cases hs : ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧ w'.under (𝓞 K) = w.under (𝓞 K)
  · obtain ⟨w', hne, hu⟩ := hs
    left
    refine ⟨?_, w', hne, hu, hgood.1 w' hne hu⟩
    rw [absNorm_pow (K := K) w, f_one hE hne hu, pow_one]
  · push_neg at hs
    have honly : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w :=
      fun w' hu => by_contra fun hne => hs w' hne hu
    have hN2 : Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 := by
      rw [absNorm_pow (K := K) w, f_two hE w honly he]
    right
    refine ⟨hN2, hgood.2 ?_⟩
    rw [normV_absNorm, normV_absNorm, hN2]

end Primes

section Main

open Classical in

private def pick {X : Type} (sat : X → Multiset ℂˣ → Prop) (w : X) : Multiset ℂˣ :=
  if h : ∃ B, sat w B then h.choose else 0

private theorem pick_spec {X : Type} {sat : X → Multiset ℂˣ → Prop} {w : X} {B : Multiset ℂˣ} (h : sat w B) :
    sat w (pick sat w) := by
  have h' : ∃ B, sat w B := ⟨B, h⟩
  rw [pick, dif_pos h']
  exact h'.choose_spec

private theorem sat_unique {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) (h' : (CG.mk σ).HasSat w B') : B = B' :=
  GlobalTheory.LFun.HasSatGL.unique ((CG.hasSat_mk σ w B).1 h) ((CG.hasSat_mk σ w B').1 h')

private theorem sat_card {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] {n : ℕ} (σ : CuspSub F n)
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (h : (CG.mk σ).HasSat w B) : Multiset.card B = n :=
  GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk σ w B).1 h)

private theorem bound_cx {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {B : Multiset ℂˣ} {c₀ c : ℝ}
    (hc : c₀ ≤ c) (hb : ∀ b ∈ B, ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧
      ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀) :
    ∀ b ∈ B.map (fun b : ℂˣ => (b : ℂ)), ‖b‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c ∧ ‖b⁻¹‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c := by
  have hN : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
    have : Ideal.absNorm w.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hmono : (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hN hc
  intro b hb'
  obtain ⟨b₀, hb₀, rfl⟩ := Multiset.mem_map.1 hb'
  obtain ⟨h1, h2⟩ := hb b₀ hb₀
  refine ⟨h1.trans hmono, ?_⟩
  have : ((b₀ : ℂ))⁻¹ = ((b₀⁻¹ : ℂˣ) : ℂ) := (Units.val_inv_eq_inv_val b₀).symm
  rw [this]
  exact h2.trans hmono

end Main

section Cnt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

private theorem cnt_congr (s : Multiset (IrrGL k)) {a b : kˣ →* ℂˣ} (h : IsUnram (a * b⁻¹)) : cnt s a = cnt s b := by
  have e : ∀ x : kˣ, ValuativeRel.valuation k (x : k) = 1 → a x = b x := fun x hx => by
    have := h x hx
    rwa [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
  unfold cnt
  congr 1
  refine Multiset.filter_congr fun y _ => exists_congr fun ξ => exists_congr fun hξ => and_congr_right fun _ => ?_
  refine forall_congr' fun x => forall_congr' fun hx => ?_
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, e x hx]

private theorem cnt_zero (s : Multiset (IrrGL k)) (a : kˣ →* ℂˣ)
    (h : ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ¬ IsUnram (ξ * a)) : cnt s a = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ξ, hξ, rfl, hu⟩
  exact h ξ hξ hy hu

private theorem cnt_zero_of_unr (s : Multiset (IrrGL k)) (a : kˣ →* ℂˣ) (hs : ∀ y ∈ s, y.IsUnramChar)
    (ha : ¬ IsUnram a) : cnt s a = 0 := by
  refine cnt_zero s a fun ξ hξ hy hu => ?_
  obtain ⟨μ, hμ, e⟩ := hs _ hy
  rw [IrrGL.ofChar_inj.1 e] at hu
  exact ha (unr_cancel hμ hu)

private theorem exists_bad (s : Multiset (IrrGL k)) :
    ∃ T : Finset (kˣ →* ℂˣ), ∀ ξ hξ, IrrGL.ofChar ξ hξ ∈ s → ξ ∈ T := by
  let g : IrrGL k → (kˣ →* ℂˣ) := fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1
  refine ⟨s.toFinset.image g, fun ξ hξ hy => Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hy, ?_⟩⟩
  have h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' := ⟨ξ, hξ, rfl⟩
  change (if h : ∃ ξ' hξ', IrrGL.ofChar ξ hξ = IrrGL.ofChar ξ' hξ' then h.choose else 1) = ξ
  rw [dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  exact (IrrGL.ofChar_inj.1 h2).symm

end Cnt

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

section Key

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private def Key (sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop) (satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop)
    (w : HeightOneSpectrum (𝓞 M)) : Prop :=
  (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ∧ ∃ w' : HeightOneSpectrum (𝓞 M), w' ≠ w ∧
    w'.under (𝓞 K) = w.under (𝓞 K) ∧ ∃ B B', sat w B ∧ sat w' B' ∧ satP (w.under (𝓞 K)) (B + B')) ∨
  (Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ 2 ∧
    ∃ B B' : Multiset ℂˣ, sat w (B'.map (· ^ 2)) ∧ B = B' + B'.map (fun b => -b) ∧ satP (w.under (𝓞 K)) B)

private theorem Key.sat {sat : HeightOneSpectrum (𝓞 M) → Multiset ℂˣ → Prop}
    {satP : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop} {w : HeightOneSpectrum (𝓞 M)} (h : Key sat satP w) :
    (∃ B, sat w B) ∧ ∃ B, satP (w.under (𝓞 K)) B := by
  rcases h with ⟨-, w', -, -, B, B', h1, -, h⟩ | ⟨-, B, B', h1, -, h⟩
  · exact ⟨⟨_, h1⟩, _, h⟩
  · exact ⟨⟨_, h1⟩, _, h⟩

private theorem key_twist [IsTotallyComplex K] [IsTotallyComplex M] (h2 : Module.finrank K M = 2)
    {P : CuspSub K (2 * 2)} {π : CuspSub M 2} (χ : HChar K) (ξ : HChar M)
    (hξ : ∀ w : HeightOneSpectrum (𝓞 M), χ.UnrAt (w.under (𝓞 K)) →
      ξ.UnrAt w ∧ ξ.val w = χ.val (w.under (𝓞 K)) ^ (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)
    {w : HeightOneSpectrum (𝓞 M)} (hu : χ.UnrAt (w.under (𝓞 K))) (h : Key (CG.mk π).HasSat (CG.mk P).HasSat w) :
    Key (CG.mk (π.twist ξ)).HasSat (CG.mk (P.twist χ)).HasSat w := by
  simp only [← CG.twist_mk]
  rcases h with ⟨hN, w', hne, hw', B, B', hB, hB', hBP⟩ | ⟨hN, B, B', hB, rfl, hBP⟩
  · obtain ⟨u1, v1⟩ := hξ w hu
    obtain ⟨u2, v2⟩ := hξ w' (hw' ▸ hu)
    rw [f_one h2 hne hw', pow_one] at v1
    rw [f_one h2 hne.symm hw'.symm, pow_one, hw'] at v2
    refine Or.inl ⟨hN, w', hne, hw', _, _, hB.twist u1, hB'.twist u2, ?_⟩
    have hP := hBP.twist hu
    rw [Multiset.map_add] at hP
    rwa [v1, v2]
  · obtain ⟨u1, v1⟩ := hξ w hu
    have hf : (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal = 2 :=
      Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm (w.under (𝓞 K)))
        ((absNorm_pow (K := K) w).symm.trans hN)
    rw [hf] at v1
    refine Or.inr ⟨hN, _, B'.map (· * χ.val (w.under (𝓞 K))), ?_, rfl, ?_⟩
    · have h := hB.twist u1
      rw [v1, Multiset.map_map] at h
      rw [Multiset.map_map]
      convert h using 2
      simp [mul_pow]
    · have h := hBP.twist hu
      simpa [Multiset.map_add, Multiset.map_map, Function.comp_def] using h

private theorem core [IsTotallyComplex K] [IsTotallyComplex M] (hOps : PairGOps) (hCross : CrossG) (hSide : SideG)
    (h2 : Module.finrank K M = 2) (P : CuspSub K (2 * 2)) (π : CuspSub M 2) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hkey : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S → Key (CG.mk π).HasSat (CG.mk P).HasSat w)
    (hK : GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S)
    (hM : ∀ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M, w.under (𝓞 K) ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (sK : ∀ u : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (u.adicCompletion K)))
    (sM : ∀ w : HeightOneSpectrum (𝓞 M), Multiset (IrrGL (w.adicCompletion M)))
    (hsK : ∀ u, SuppAt P u (sK u)) (hsM : ∀ w, SuppAt π w (sM w))
    (zK : ∀ u ∈ S, u ≠ v → cnt (sK u) 1 = 0)
    (zM : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∈ S → w.under (𝓞 K) ≠ v → cnt (sM w) 1 = 0) :
    cnt (sK v) 1 = ∑ w : PlacesOver M v, fdeg w * cnt (sM w.1) 1 := by
  obtain ⟨cP, hcP⟩ := satBd K (2 * 2) P
  obtain ⟨cπ, hcπ⟩ := satBd M 2 π
  have hfin := finite_above (M := M) (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet
  obtain ⟨SM, hSM⟩ : ∃ SM : Finset (HeightOneSpectrum (𝓞 M)), SM = hfin.toFinset := ⟨_, rfl⟩
  have memSM : ∀ w, w ∈ SM ↔ w.under (𝓞 K) ∈ S := fun w => by
    rw [hSM, Set.Finite.mem_toFinset]; rfl
  obtain ⟨BK, hBK⟩ : ∃ BK, BK = pick (CG.mk P).HasSat := ⟨_, rfl⟩
  obtain ⟨BM, hBM⟩ : ∃ BM, BM = pick (CG.mk π).HasSat := ⟨_, rfl⟩
  have satK : ∀ p ∉ S, (CG.mk P).HasSat p (BK p) := fun p hp => by
    obtain ⟨w, rfl⟩ := exists_over (M := M) p
    rw [hBK]
    obtain ⟨B, h⟩ := (hkey w hp).sat.2
    exact pick_spec h
  have satM : ∀ w ∉ SM, (CG.mk π).HasSat w (BM w) := fun w hw => by
    rw [hBM]
    obtain ⟨B, h⟩ := (hkey w fun h => hw ((memSM w).2 h)).sat.1
    exact pick_spec h
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨β, Q, hβ, hQ0, hQd, pK⟩ := hSide K (2 * 2) (by norm_num) P S hK BK satK sK _ (fun _ => 1) hq
    fun u hu => ⟨hsK u, fun h => by
      rw [pow_one, not_not.1 fun e => h (zK u hu e)]⟩
  obtain ⟨β', Q', hβ', hQ0', hQd', pM⟩ := hSide M 2 le_rfl π SM (fun w hw => (memSM w).2 (hM w hw)) BM satM sM _
    (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq fun w hw => ⟨hsM w, fun h => by
      have e : w.under (𝓞 K) = v := not_not.1 fun e => h (zM w ((memSM w).1 hw) e)
      rw [← e]
      exact absNorm_pow w⟩
  obtain ⟨c, hc⟩ := regroup K M h2 (S : Set (HeightOneSpectrum (𝓞 K))) (SM : Set (HeightOneSpectrum (𝓞 M))) (cx BK) (cx BM)
    (max cP cπ) 4 (fun w => by simpa using memSM w)
    (fun p hp => by
      have hs := satK p (by simpa using hp)
      refine ⟨by simp [cx, sat_card P hs], bound_cx p (le_max_left cP cπ) (hcP p _ hs)⟩)
    (fun w hw => by
      have hs := satM w (by simpa using hw)
      refine ⟨by simp [cx, sat_card π hs], bound_cx w (le_max_right cP cπ) (hcπ w _ hs)⟩)
    (fun w hw => by
      have hw₁ : w ∉ SM := by simpa using hw
      have hw' : w.under (𝓞 K) ∉ S := fun h => hw₁ ((memSM w).2 h)
      have s1 := satK _ hw'
      have s2 := satM w hw₁
      rcases hkey w hw' with ⟨hN, w', hne, hu, B, B', h1, h3, h4⟩ | ⟨hN, B, B', h1, h3, h4⟩
      · left
        refine ⟨hN, w', hne, hu, ?_⟩
        have s3 := satM w' fun h => hw' (hu ▸ (memSM w').1 h)
        rw [cx, cx, cx, sat_unique P s1 h4, sat_unique π s2 h1, sat_unique π s3 h3, Multiset.map_add]
      · right
        refine ⟨hN, B'.map fun b : ℂˣ => (b : ℂ), ?_, ?_⟩
        · rw [cx, sat_unique π s2 h1, Multiset.map_map, Multiset.map_map]
          exact Multiset.map_congr rfl fun b _ => by simp
        · rw [cx, sat_unique P s1 h4, h3, Multiset.map_add, Multiset.map_map, Multiset.map_map]
          congr 1)
  have pM' := hOps.2.2.1 _ _ _ _ _ _ _ c pM (fun s hs => ((hc s).1 hs).symm) (fun s hs => ((hc s).2 hs).symm)
  have e := hCross _ _ _ _ _ _ _ (by exact_mod_cast hq) hβ hβ' hQ0 hQ0' pK pM'
  rw [e, hQd', Finset.sum_eq_single_of_mem v hv (fun u hu hne => by rw [zK u hu hne, mul_zero]), one_mul] at hQd
  rw [← hQd]
  have hsub : (Finset.univ : Finset (PlacesOver M v)).map (Function.Embedding.subtype _) ⊆ SM := by
    intro w hw
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hw
    have : w.1.under (𝓞 K) = v := HeightOneSpectrum.ext w.2.over.symm
    exact (memSM w.1).2 (by rw [this]; exact hv)
  rw [← Finset.sum_subset hsub (fun w hw hw' => ?_), Finset.sum_map]
  · rfl
  · rw [zM w ((memSM w).1 hw) fun e => hw' ?_, mul_zero]
    exact Finset.mem_map.2 ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal e.symm⟩⟩, Finset.mem_univ _, rfl⟩

private theorem norm_units (h2 : Module.finrank K M = 2) :
    (∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ T, ∀ (w : PlacesOver M u) (θ : (u.adicCompletion K)ˣ →* ℂˣ),
      IsSmoothChar θ → IsUnram (θ.comp (nm w)) → IsUnram θ) ∧
    ∀ (u : HeightOneSpectrum (𝓞 K)) (w : PlacesOver M u) (θ : (u.adicCompletion K)ˣ →* ℂˣ), IsUnram θ →
      IsUnram (θ.comp (nm w)) := by
  haveI : Algebra.IsQuadraticExtension K M := { finrank_eq_two' := h2 }
  obtain ⟨η, h1, h3⟩ := normCnt K M (h2 ▸ Nat.prime_two)
  refine ⟨⟨(Filter.eventually_cofinite.1 h1).toFinset, fun u hu w θ hθ hn => ?_⟩,
    fun u w θ hθ => ((h3 u w).2.2 θ (isSmoothChar_of_isUnram hθ)).2.1 hθ⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu
  have hc := ((h3 u w).2.2 θ hθ).2.2 hn
  have hpos : 0 < ∑ w' : PlacesOver M u, fdeg w' := by
    have hw := (hu.2 w).2
    have : 0 < fdeg w := Nat.pos_of_ne_zero fun e => by rw [e, h2] at hw; omega
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun w' : PlacesOver M u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hj' := (Finset.mem_filter.1 hj).2
  have hη : IsUnram ((η ^ j).loc u) := fun x hx => by
    have e : (η ^ j).loc u x = η.loc u x ^ j := MonoidHom.pow_apply η.1 j _
    rw [e, (unrAt_iff η u).1 hu.1 x hx, one_pow]
  exact unr_cancel hη (mul_comm θ _ ▸ hj')

end Key

end InductionMatchingPlacesAbove

open InductionMatchingPlacesAbove in
theorem matchIndOf : MatchIndOf := by
  intro hOps hCross hSide hSupp hNL hTw K M _ _ _ _ _ _ _ h2 P π hI v s s' hs hs' θ hθ
  obtain ⟨S₁, hkey⟩ := ind_key h2 _ _ hI
  obtain ⟨⟨T, hT⟩, hnm⟩ := norm_units h2
  have FK := hSupp K (2 * 2) (by norm_num) P
  have FM := hSupp M 2 (by norm_num) π
  choose sK hsK using fun u => (FK u).1
  choose sM hsM using fun w => (FM w).1
  choose bK hbK using fun u => exists_bad (sK u)
  choose bM hbM using fun w => exists_bad (sM w)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S₀ ↔ u = v ∨ u ∈ S₁ ∨ u ∈ T ∨
      u ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∨
      ∃ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M, w.under (𝓞 K) = u :=
    ⟨insert v (S₁ ∪ (T ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∪
      (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M).image fun w => w.under (𝓞 K)))), fun u => by simp⟩
  obtain ⟨χ, hχv, hχ⟩ := hTw K M v θ hθ S₀ bK bM
  obtain ⟨ξ, hξ⟩ := hNL K M χ
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ χ.UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset, fun u => by simp⟩
  choose tK htK using fun u => (FK u).2.2.2.2 χ _ (hsK u)
  choose tM htM using fun w => (FM w).2.2.2.2 ξ _ (hsM w)
  have k₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S₀ → Key (CG.mk π).HasSat (CG.mk P).HasSat w :=
    fun w hw => hkey w fun h => hw ((hS₀ _).2 (Or.inr (Or.inl h)))
  have main := core hOps hCross hSide h2 (P.twist χ) (π.twist ξ) S
    (fun w hw => key_twist h2 χ ξ (fun w hu => (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).2.1 hu)
      (not_not.1 fun h => hw ((hS _).2 (Or.inr h))) (k₀ w fun h => hw ((hS _).2 (Or.inl h))))
    (fun u hu => (hS _).2 (Or.inl ((hS₀ _).2 (by tauto))))
    (fun w hw => (hS _).2 (Or.inl ((hS₀ _).2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)))))))
    v ((hS _).2 (Or.inl ((hS₀ _).2 (Or.inl rfl)))) tK tM (fun u => (htK u).1) (fun w => (htM w).1)
    (fun u hu hne => by
      rw [(htK u).2.1, mul_one]
      by_cases h0 : u ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ u h0 hne).1 ζ (hbK u ζ hζ hy)
      · obtain ⟨w, rfl⟩ := exists_over (M := M) u
        obtain ⟨B, hB⟩ := (k₀ w h0).sat.2
        exact cnt_zero_of_unr _ _ ((FK _).2.2.2.1 _ B (hsK _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2 h))
    (fun w hu hne => by
      rw [(htM w).2.1, mul_one, (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 K) ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ _ h0 hne).2 ⟨w, ⟨rfl⟩⟩ ζ (hbM w ζ hζ hy)
      · obtain ⟨B, hB⟩ := (k₀ w h0).sat.1
        exact cnt_zero_of_unr _ _ ((FM _).2.2.2.1 _ B (hsM _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2
            (hT _ (fun h' => h0 ((hS₀ _).2 (by tauto))) _ _ (GlobalTheory.HeckeComp.smooth_loc χ _) h)))
  rw [(htK v).2.1, mul_one, cnt_congr _ hχv, (FK v).2.1 _ _ (hsK v) hs] at main
  rw [main]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [(htM w.1).2.1, mul_one, (hξ v w).1, (FM w.1).2.1 _ _ (hsM w.1) (hs' w)]
  congr 1
  exact cnt_congr _ (hnm v w _ hχv)

end UpperTheory.V.Z.Gam
