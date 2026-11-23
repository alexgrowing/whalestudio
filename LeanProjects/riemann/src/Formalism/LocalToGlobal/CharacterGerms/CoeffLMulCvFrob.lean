import Formalism.LocalToGlobal.CharacterGerms.GermEvalOneStandardPointSelf
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroFirstThenZero

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace FirstVanishing

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence

variable {C : Type} [Field C] [CharZero C] {V : VF C}

theorem intS_cv {γ : PowerSeries C} (h : ∀ n, V.Ge 0 (PowerSeries.coeff n γ)) : IntS V γ := by
  intro μ
  have hμ : μ = Finsupp.single () (μ ()) := by
    ext u
    simp
  rw [hμ]
  exact h (μ ())

theorem degree_one {σ : Type} {ν : σ →₀ ℕ} (h : ν.degree = 1) : ∃ s, ν = Finsupp.single s 1 := by
  classical
  have hsum : ν.degree = ∑ t ∈ ν.support, ν t := rfl
  obtain ⟨s, hs⟩ : ∃ s, ν s ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : ν = 0 := Finsupp.ext hall
    rw [h0] at h
    simp at h
  have hmem : s ∈ ν.support := Finsupp.mem_support_iff.mpr hs
  have htot := Finset.add_sum_erase ν.support (fun t => ν t) hmem
  rw [← hsum, h] at htot
  have hs1 : ν s = 1 := by omega
  have hrest0 : ∑ t ∈ ν.support.erase s, ν t = 0 := by omega
  have hrest : ∀ t, t ≠ s → ν t = 0 := by
    intro t ht
    by_cases htm : t ∈ ν.support
    · exact (Finset.sum_eq_zero_iff.mp hrest0) t (Finset.mem_erase.mpr ⟨ht, htm⟩)
    · by_contra hne
      exact htm (Finsupp.mem_support_iff.mpr hne)
  refine ⟨s, ?_⟩
  ext t
  by_cases ht : t = s
  · subst ht
    simp [hs1]
  · rw [Finsupp.single_apply, if_neg (Ne.symm ht), hrest t ht]

theorem divisible_small {σ : Type} {l : ℕ} (μ : σ →₀ ℕ) (hdiv : ∀ s, l ∣ μ s)
    (hdeg : μ.degree < 2 * l) : μ = 0 ∨ ∃ s, μ = Finsupp.single s l := by
  classical
  by_cases h0 : μ = 0
  · exact Or.inl h0
  right
  have hsum : μ.degree = ∑ t ∈ μ.support, μ t := rfl
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact h0 (Finsupp.ext hall)
  have hmem : s ∈ μ.support := Finsupp.mem_support_iff.mpr hs
  have htot := Finset.add_sum_erase μ.support (fun t => μ t) hmem
  rw [← hsum] at htot
  obtain ⟨k, hk⟩ := hdiv s
  have hk1 : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact hs hk
  have hl0 : 0 < l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h
      simp at hk
      exact absurd hk hs
    · exact h
  have hk2 : k = 1 := by
    by_contra hk2
    have : 2 * l ≤ μ s := by
      rw [hk]
      have : 2 ≤ k := by omega
      nlinarith
    omega
  subst hk2
  rw [mul_one] at hk
  have hrest0 : ∑ t ∈ μ.support.erase s, μ t < l := by omega
  have hrest : ∀ t, t ≠ s → μ t = 0 := by
    intro t ht
    by_contra hne
    have htm : t ∈ μ.support.erase s := Finset.mem_erase.mpr ⟨ht, Finsupp.mem_support_iff.mpr hne⟩
    have hle : μ t ≤ ∑ t ∈ μ.support.erase s, μ t :=
      Finset.single_le_sum (f := fun t => μ t) (fun _ _ => Nat.zero_le _) htm
    obtain ⟨m, hm⟩ := hdiv t
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      exact hne hm
    have : l ≤ μ t := by
      rw [hm]
      exact Nat.le_mul_of_pos_right l (Nat.pos_of_ne_zero hm0)
    omega
  refine ⟨s, ?_⟩
  ext t
  by_cases ht : t = s
  · subst ht
    simp [hk]
  · rw [Finsupp.single_apply, if_neg (Ne.symm ht), hrest t ht]

theorem coeff_subst_scale {dd : ℕ} (f : MvPowerSeries (Fin dd) C) (U : Fin dd → C) (c : C) (n : ℕ) :
    PowerSeries.coeff n (MvPowerSeries.subst (fun j => (c * U j) • (MvPowerSeries.X () : PowerSeries C)) f) =
      c ^ n * PowerSeries.coeff n (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) f) := by
  have hX0 : ∀ (a : C) (s : Unit), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X s : PowerSeries C)) = 0 := by
    intro a s
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hU : MvPowerSeries.HasSubst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => hX0 _ _
  have hc : MvPowerSeries.HasSubst ((fun _ : Unit => c) • (MvPowerSeries.X : Unit → PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hX0 c s
  have h1 : MvPowerSeries.subst (fun j => (c * U j) • (MvPowerSeries.X () : PowerSeries C)) f =
      MvPowerSeries.subst ((fun _ : Unit => c) • (MvPowerSeries.X : Unit → PowerSeries C))
        (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) f) := by
    rw [MvPowerSeries.subst_comp_subst_apply hU hc]
    congr 1
    funext j
    rw [MvPowerSeries.subst_smul hc, MvPowerSeries.subst_X hc]
    show (c * U j) • (MvPowerSeries.X () : PowerSeries C) = U j • ((c : C) • (MvPowerSeries.X () : PowerSeries C))
    rw [smul_smul, mul_comm]
  rw [h1, ← MvPowerSeries.rescale_eq_subst]
  change MvPowerSeries.coeff (Finsupp.single () n) _ = c ^ n * MvPowerSeries.coeff (Finsupp.single () n) _
  rw [MvPowerSeries.coeff_rescale, Finsupp.prod_single_index (by simp)]

section Main

variable {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem Agr.smul {τ : Type} {k : ℕ} {f g : MvPowerSeries τ C} (h : Agr k f g) (c : C) : Agr k (c • f) (c • g) :=
  fun e he => by rw [map_smul, map_smul, h e he]

theorem lg_mulCv (Y : FBChart C V O dd) (p : PairData Y d I) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0) (n : ℕ) (j : Fin dd) :
    MvPowerSeries.subst (fun k => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k))
        ((Y.raw p).lg j) = (n : C) • alongCv γ ((Y.raw p).lg j) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hM : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => mulL Y.B.G.F n q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F n k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G n k)
  have h := congrArg (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2)) (MulLFrob.lg_mulL Y n j)
  rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply hM hG,
    show (n • Y.lg j) = (n : C) • Y.lg j from (Nat.cast_smul_eq_nsmul C n _).symm,
    MvPowerSeries.subst_smul hG] at h
  show MvPowerSeries.subst _ (un1 (Y.lg j)) = (n : C) • MvPowerSeries.subst γ (un1 (Y.lg j))
  rw [subst_singlePointUncurry hL0, subst_singlePointUncurry hγ0]
  exact h

theorem coeff_l_mulCv (Y : FBChart C V O dd) (p : PairData Y d I) {g : Fin 2} {w : I g → C}
    {x : ℕ → I g ⊕ JJ I g → C} (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
    (hlg : ∀ i, alongCv γ ((Y.raw p).lg i) = ∑ c : I g, (Y.raw p).u g c i • tyS V.l (fun s => x s (Sum.inl c)))
    (k : Fin dd) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hL0 : ∀ k, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_subst_eq_zero hG (fun q => hγ0 q.2) (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k)
  set U : Fin dd → C := fun j => ∑ c, (Y.raw p).u g c j * w c with hU
  have hX0 : ∀ (a : C), MvPowerSeries.constantCoeff (a • (MvPowerSeries.X () : PowerSeries C)) = 0 := by
    intro a
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hcl : ∀ j, MvPowerSeries.constantCoeff (alongCv γ ((Y.raw p).lg j)) = 0 := fun j =>
    MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0) hγ0
      (Y.chart_log_constantCoeff p j)

  have eL := ex_lg_at Y p _ hL0 k
  simp only [lg_mulCv Y p hγ0 V.l] at eL
  have hAL : Agr (V.l ^ 2) (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k))
      (MvPowerSeries.subst (fun j => ((V.l : C) * U j) • (MvPowerSeries.X () : PowerSeries C)) ((Y.raw p).ex k)) := by
    rw [← eL]
    refine agr_subst_left (fun j => by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hcl j, mul_zero])
      (fun j => hX0 _) (fun j => ?_) _
    have := Agr.smul (lgCv_agr Y p h0 h1 hlg j) (V.l : C)
    rwa [smul_smul] at this

  have eG := ex_lg_at Y p γ hγ0 k
  have hAG : Agr (V.l ^ 2) (γ k)
      (MvPowerSeries.subst (fun j => U j • (MvPowerSeries.X () : PowerSeries C)) ((Y.raw p).ex k)) := by
    rw [← eG]
    exact agr_subst_left hcl (fun j => hX0 _) (fun j => lgCv_agr Y p h0 h1 hlg j) _
  have hdeg : (Finsupp.single () V.l).degree < V.l ^ 2 := by
    rw [Finsupp.degree_single]
    nlinarith
  have e1 := hAL _ hdeg
  have e2 := hAG _ hdeg
  change PowerSeries.coeff V.l _ = PowerSeries.coeff V.l _ at e1 e2
  rw [e1, FirstVanishing.coeff_subst_scale, ← e2]
  obtain ⟨m, hm⟩ : ∃ m, V.l = m + 1 := ⟨V.l - 1, by omega⟩
  have e3 : (V.l : C) ^ V.l = (V.l : C) * (V.l : C) ^ m := by
    rw [← pow_succ', ← hm]
  rw [e3, mul_assoc]
  exact mm_l_mul ((VF.Ge.pow (ge_natCast V.l) m).mul_int ((hγ k).2 V.l))

end Main

section Frob

variable {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem coeff_l_mulCv_frob (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (k : Fin dd) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (mulL Y.B.G.F V.l k)) -
      ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) *
        (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hγ0' : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := hγ0
  have hP : IntS V (mulL Y.B.G.F V.l k) := FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l k
  have hPz : MvPowerSeries.constantCoeff (mulL Y.B.G.F V.l k) = 0 := FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l k
  have hfrob : ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (mulL Y.B.G.F V.l k)) :=
    fun μ hμ => mulLFrob_holds C V O dd Y k μ hμ
  generalize mulL Y.B.G.F V.l k = P at hP hPz hfrob ⊢
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) V.l)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) := ⟨_, rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr (2 * V.l) (P - D1 - D3) 0 := by
    intro μ hμ
    rw [map_sub, map_sub, map_zero, hD1def, hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      obtain ⟨i', hi'⟩ := hex
      apply hi'
      rw [Finsupp.single_apply]
      split_ifs
      · exact dvd_refl _
      · exact dvd_zero _
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv hμ with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun i _ => if_neg ?_
        intro h
        have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
        omega
      · subst hs
        rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s, sub_self]
        · intro i _ hi
          rw [if_neg]
          intro h
          apply hi
          have := (Finsupp.single_left_inj (by omega : V.l ≠ 0)).1 h
          rw [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hsplit : P = D1 + (P - D1 - D3) + D3 := by ring
  have hdeg : (Finsupp.single () V.l).degree < 2 * V.l := by
    rw [Finsupp.degree_single]
    omega
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) hD2)
    (Finsupp.single () V.l) hdeg
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3)) = 0 :=
    hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () V.l)
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) * γ i ^ V.l := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  have hfr : ∀ i, V.MM (PowerSeries.coeff V.l (γ i ^ V.l) - (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
    intro i
    have h := mms_pow_frobTw (hγI i) (Finsupp.single () V.l)
    rw [map_sub, coeff_frobTw, if_pos (fun s => by simp)] at h
    have e : (Finsupp.single () V.l).mapRange (fun n => n / V.l) (Nat.zero_div V.l) = Finsupp.single () 1 := by
      rw [Finsupp.mapRange_single, Nat.div_self (by omega)]
    rw [e] at h
    exact h
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3) +
          MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 := by
    conv_lhs => rw [hsplit]
    rw [MvPowerSeries.subst_add hG, MvPowerSeries.subst_add hG]
  rw [eP, map_add, map_add, hA2', add_zero, hD3, map_sum]
  have e : ∀ (a : C) (s t : Fin dd → C),
      a + ∑ i, s i - ∑ i, t i = a + ∑ i, (s i - t i) := fun a s t => by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  refine mm_add hB1 (mm_sum _ _ fun i _ => ?_)
  rw [show PowerSeries.coeff V.l (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) *
      γ i ^ V.l) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * PowerSeries.coeff V.l (γ i ^ V.l) from
    MvPowerSeries.coeff_C_mul _ _ _, ← mul_sub]
  exact mm_mul_ge' (hP _) (hfr i)

end Frob

end FirstVanishing

theorem first_vanishing : GoodVectorsMulPrimePowerCoefficientsVanish := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk Hc hAlt g a hbig w x hG hc0 γ lam hW k
  have hB := FirstVanishing.coeff_l_mulCv Y p hG.1.2.1 hG.2 hW.1 hW.2.2.1 k
  have hA := FirstVanishing.coeff_l_mulCv_frob Y hW.1 k
  have h := MaximalIdealCongruence.mm_sub hB hA
  rwa [sub_sub_cancel] at h

end Formalism.L2.FormalSeriesBounds
