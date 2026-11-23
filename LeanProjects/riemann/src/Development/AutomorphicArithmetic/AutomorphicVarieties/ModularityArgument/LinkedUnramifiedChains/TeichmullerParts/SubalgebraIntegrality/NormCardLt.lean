import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.J.D

namespace UpperTheory.V.Z.J.D

section Emb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {l : ℕ} [Fact l.Prime]

private theorem norm_unif_lt (j : k →+* Qbar l) (hj : Continuous j) : ‖j (unif k : k)‖ < 1 := by
  have hv : Tendsto (fun n : ℕ => ((unif k : kˣ) : k) ^ n) atTop (nhds 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt₀ (ValuativeRel.uniformizer_lt_one (R := k)) γ
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Set.mem_setOf_eq, map_pow, GlAx.unif_spec]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' ValuativeRel.uniformizer_lt_one.le hn) hN
  have hj' : Tendsto (fun n : ℕ => (j (unif k : k)) ^ n) atTop (nhds 0) := by
    have := (hj.tendsto 0).comp hv
    simpa [Function.comp_def, map_pow] using this
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hj'

end Emb

section Pow

variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (w : Plc L)

private theorem pow_ne (h : (L →+* Qbar l) → ℤ) :
    algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (Units.ne_zero _))

private theorem pow_anti {h h' : (L →+* Qbar l) → ℤ} (hh : ∀ τ, h τ ≤ h' τ) :
    ‖algPow w h' ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ ≤
      ‖algPow w h ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ := by
  classical
  haveI : Finite {j : w.adicCompletion L →+* Qbar l // Continuous j} :=
    GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, norm_prod, norm_prod]
  refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [norm_zpow, norm_zpow]
  have hlt := norm_unif_lt (k := w.adicCompletion L) (l := l) j.1 j.2
  have hpos : 0 < ‖j.1 ((unif (w.adicCompletion L) : (w.adicCompletion L)ˣ) : w.adicCompletion L)‖ :=
    norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr (Units.ne_zero _))
  exact zpow_le_zpow_right_of_le_one₀ hpos hlt.le (hh _)

private theorem card_dvd (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) : l ∣ Nat.card 𝓀[w.adicCompletion L] := by
  have hc : Nat.card 𝓀[w.adicCompletion L] = Nat.card (𝓞 L ⧸ w.asIdeal) := by
    have := GlobalTheory.LocLanglands.resCard_eq_normV (E := L) w
    simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV] using this
  rw [hc]
  haveI := w.isPrime
  have hz : ((l : ℕ) : 𝓞 L ⧸ w.asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := w.asIdeal)).mpr hl
    simpa using this
  have hdvd : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) ∣ l := by
    apply addOrderOf_dvd_of_nsmul_eq_zero
    simpa [nsmul_eq_mul] using hz
  have hord : addOrderOf (1 : 𝓞 L ⧸ w.asIdeal) = l := by
    rcases (Nat.dvd_prime (Fact.out : l.Prime)).mp hdvd with h | h
    · have h1 := addOrderOf_nsmul_eq_zero (1 : 𝓞 L ⧸ w.asIdeal)
      rw [h, one_nsmul] at h1
      exact absurd h1 one_ne_zero
    · exact h
  rw [← hord]
  exact addOrderOf_dvd_natCard _

private theorem norm_card_lt (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ‖((Nat.card 𝓀[w.adicCompletion L] : ℕ) : Qbar l)‖ < 1 := by
  obtain ⟨m, hm⟩ := card_dvd w hl
  rw [hm, Nat.cast_mul, ← map_natCast (algebraMap ℚ_[l] (Qbar l)) l,
    ← map_natCast (algebraMap ℚ_[l] (Qbar l)) m, ← map_mul]
  have he : ‖algebraMap ℚ_[l] (Qbar l) ((l : ℚ_[l]) * (m : ℚ_[l]))‖ = ‖(l : ℚ_[l]) * (m : ℚ_[l])‖ :=
    PadicAlgCl.norm_extends l _
  rw [he, norm_mul]
  have hm1 : ‖(m : ℚ_[l])‖ ≤ 1 := by
    simpa using Padic.norm_int_le_one (p := l) (m : ℤ)
  calc ‖(l : ℚ_[l])‖ * ‖(m : ℚ_[l])‖ ≤ ‖(l : ℚ_[l])‖ * 1 :=
        mul_le_mul_of_nonneg_left hm1 (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact Padic.norm_p_lt_one

end Pow

private theorem prod_le {M : Type} [CommMonoid M] {n : ℕ} (f : ℕ → M) (j : Fin n) :
    ∏ i with i ≤ j, f (i : ℕ) = ∏ k ∈ Finset.range (j + 1), f k := by
  classical
  refine Finset.prod_nbij (fun i : Fin n => (i : ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_range]
    have : (i : ℕ) ≤ (j : ℕ) := hi
    omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show k ≤ (j : ℕ)
    omega
  · intro i _
    rfl

private theorem prod_tele {U : ℕ → ℂ} (h : ∀ k, U k ≠ 0) (m : ℕ) :
    ∏ k ∈ Finset.range m, U (k + 1) / U k = U m / U 0 := by
  induction m with
  | zero => simp [h 0]
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    field_simp [h m, h 0]

private theorem exp_core {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (a : Fin n → Qbar l) (u : Fin n → ℂ) (q : ℕ)
    (ha : ∀ i, a i ≠ 0) (hanti : ∀ i i', i ≤ i' → ‖a i'‖ ≤ ‖a i‖) (hq0 : (q : Qbar l) ≠ 0)
    (hq1 : ‖(q : Qbar l)‖ < 1) (hu : ∀ j, ‖ι.symm (u j)‖ = 1) :
    ∃ ω : Fin n → ℂˣ, Function.Injective ω ∧ ∀ j : Fin n,
      ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) * u j =
        ∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹ := by
  classical
  have hq0' : (q : ℂ) ≠ 0 := by
    intro h
    apply hq0
    have : q = 0 := by exact_mod_cast h
    simp [this]
  have hqpos : 0 < ‖(q : Qbar l)‖ := norm_pos_iff.mpr hq0
  let A : ℕ → Qbar l := fun k => if h : k < n then a ⟨k, h⟩ else 1
  let W : ℕ → Qbar l := fun k => if h : k < n then ι.symm (u ⟨k, h⟩) else 1
  have hAne : ∀ k, A k ≠ 0 := by
    intro k
    by_cases h : k < n
    · simp only [A, dif_pos h]; exact ha _
    · simp only [A, dif_neg h]; exact one_ne_zero
  have hWn : ∀ k, ‖W k‖ = 1 := by
    intro k
    by_cases h : k < n
    · simp only [W, dif_pos h]; exact hu _
    · simp only [W, dif_neg h]; exact norm_one
  have hWne : ∀ k, W k ≠ 0 := fun k => norm_ne_zero_iff.mp (by rw [hWn k]; exact one_ne_zero)
  let T : ℕ → Qbar l := fun k =>
    (∏ i ∈ Finset.range (k + 1), A i) * W k * ∏ i ∈ Finset.range (k + 1), (q : Qbar l) ^ i
  have hTne : ∀ k, T k ≠ 0 := by
    intro k
    refine mul_ne_zero (mul_ne_zero ?_ (hWne k)) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hAne i
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hq0
  let Tm : ℕ → Qbar l := fun k => if k = 0 then 1 else T (k - 1)
  have hTm0 : Tm 0 = 1 := by simp [Tm]
  have hTms : ∀ k, Tm (k + 1) = T k := by intro k; simp [Tm]
  have hTmne : ∀ k, Tm k ≠ 0 := by
    intro k
    rcases k with _ | k
    · rw [hTm0]; exact one_ne_zero
    · rw [hTms]; exact hTne k
  let U : ℕ → ℂ := fun k => ι (Tm k)
  have hUne : ∀ k, U k ≠ 0 := fun k => (_root_.map_ne_zero ι).mpr (hTmne k)
  let ω : Fin n → ℂˣ := fun i =>
    Units.mk0 (U ((i : ℕ) + 1) / U i) (div_ne_zero (hUne _) (hUne _))
  let G : ℕ → ℝ := fun k => ∏ i ∈ Finset.range k, (‖A i‖ * ‖(q : Qbar l)‖ ^ i)
  have hGs : ∀ k, G (k + 1) = G k * (‖A k‖ * ‖(q : Qbar l)‖ ^ k) :=
    fun k => Finset.prod_range_succ _ _
  have hG : ∀ k, k ≤ n → ‖Tm k‖ = G k := by
    intro k hk
    rcases k with _ | k
    · rw [hTm0, norm_one]; rfl
    · rw [hTms]
      simp only [T, G, norm_mul, norm_prod, norm_pow, hWn k, mul_one, Finset.prod_mul_distrib]
  have hGne : ∀ k, G k ≠ 0 := by
    intro k
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      mul_ne_zero (norm_ne_zero_iff.mpr (hAne i)) (pow_ne_zero _ hqpos.ne')
  have hnorm : ∀ i : Fin n, ‖ι.symm (ω i : ℂ)‖ = ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := by
    intro i
    have e1 : ι.symm (ω i : ℂ) = Tm ((i : ℕ) + 1) / Tm i := by
      simp only [ω, Units.val_mk0, U, map_div₀, RingEquiv.symm_apply_apply]
    rw [e1, norm_div, hG _ (Nat.succ_le_of_lt i.isLt), hG _ i.isLt.le, hGs,
      mul_div_cancel_left₀ _ (hGne _)]
    simp only [A, dif_pos i.isLt]
  have hsa : StrictAnti (fun i : Fin n => ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ)) := by
    intro i i' hii
    have h1 : ‖a i'‖ ≤ ‖a i‖ := hanti i i' hii.le
    have h2 : ‖(q : Qbar l)‖ ^ (i' : ℕ) < ‖(q : Qbar l)‖ ^ (i : ℕ) :=
      pow_lt_pow_right_of_lt_one₀ hqpos hq1 (Fin.lt_iff_val_lt_val.mp hii)
    have h3 : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    calc ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) ≤ ‖a i‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) := mul_lt_mul_of_pos_left h2 h3
  refine ⟨ω, ?_, ?_⟩
  · intro i i' h
    apply hsa.injective
    show ‖a i‖ * ‖(q : Qbar l)‖ ^ (i : ℕ) = ‖a i'‖ * ‖(q : Qbar l)‖ ^ (i' : ℕ)
    rw [← hnorm i, ← hnorm i', h]
  · intro j
    have hL : (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1, a i) =
        ∏ k ∈ Finset.range (j + 1), A k := by
      rw [← prod_le A j]
      refine Finset.prod_congr ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro h
        · exact Fin.le_iff_val_le_val.mpr (by omega)
        · have := Fin.le_iff_val_le_val.mp h
          omega
      · intro i _
        simp only [A, dif_pos i.isLt]
    have hR : (∏ i with i ≤ j, (ω i : ℂ) * ((q : ℂ) ^ (i : ℕ))⁻¹) =
        ∏ k ∈ Finset.range (j + 1), (U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) :=
      prod_le (fun k => U (k + 1) / U k * ((q : ℂ) ^ k)⁻¹) j
    have hWj : ι (W j) = u j := by simp only [W, dif_pos j.isLt, RingEquiv.apply_symm_apply]
    have hqp : (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ hq0'
    have hUj : U ((j : ℕ) + 1) =
        ι (∏ k ∈ Finset.range (j + 1), A k) * u j * ∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k := by
      simp only [U, hTms, T, map_mul, hWj, map_prod, map_pow, map_natCast]
    have hU0 : U 0 = 1 := by simp only [U, hTm0, map_one]
    rw [hL, hR, Finset.prod_mul_distrib, prod_tele hUne, Finset.prod_inv_distrib, hUj, hU0,
      div_one, mul_assoc _ (∏ k ∈ Finset.range (j + 1), (q : ℂ) ^ k), mul_inv_cancel₀ hqp, mul_one]

end UpperTheory.V.Z.J.D

theorem UpperTheory.V.Z.J.D.slope :
    Slope := by
  intro L Ω _ _ _ _ _ l _ n c H hA ι lam v u hu
  have hl := hA.Sl_over v
  obtain ⟨ω, h1, h2⟩ := exp_core ι
    (fun i => algPow (H.Sl v) (lowW lam i) ((unif ((H.Sl v).adicCompletion L) : ((H.Sl v).adicCompletion L)ˣ) : (H.Sl v).adicCompletion L))
    u (Nat.card 𝓀[(H.Sl v).adicCompletion L]) (fun i => pow_ne _ _)
    (fun i i' h => pow_anti _ fun τ => (lam τ).anti (Fin.rev_le_rev.2 h))
    (Nat.cast_ne_zero.2 Nat.card_pos.ne') (norm_card_lt _ hl) hu
  exact ⟨ω, h1, fun j => h2 j⟩
