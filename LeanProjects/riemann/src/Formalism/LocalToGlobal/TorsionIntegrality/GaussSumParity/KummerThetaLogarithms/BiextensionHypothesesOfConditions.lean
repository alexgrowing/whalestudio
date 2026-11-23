import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Formalism.GaussJetBounds.GaussJetProofs.Transfer

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)

namespace B4

section Lin

variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]

theorem linEL_congr (σ : K →+* K) (c : K) {L L' : ZMod d → MvPowerSeries τ K}
    (h : ∀ s : ZMod d, s.val % 2 = 0 → L s = L' s) : linEL σ c L = linEL σ c L' := by
  unfold linEL
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rw [h s hs]
  · rfl

theorem linOL_congr (σ : K →+* K) (c : K) {L L' : ZMod d → MvPowerSeries τ K}
    (h : ∀ s : ZMod d, ¬ s.val % 2 = 0 → L s = L' s) : linOL σ c L = linOL σ c L' := by
  unfold linOL
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rfl
  · rw [h s hs]

theorem linEL_add (σ : K →+* K) (c : K) (L L' : ZMod d → MvPowerSeries τ K) :
    linEL σ c (fun s => L s + L' s) = linEL σ c L + linEL σ c L' := by
  unfold linEL
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [mul_add]
  · rw [add_zero]

theorem linOL_add (σ : K →+* K) (c : K) (L L' : ZMod d → MvPowerSeries τ K) :
    linOL σ c (fun s => L s + L' s) = linOL σ c L + linOL σ c L' := by
  unfold linOL
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [add_zero]
  · rw [mul_add]

end Lin

section Five

variable {K : Type} [Field K] {τ : Type} {d : ℕ} {a : V2 d → MvPowerSeries τ K}

theorem subst_first_coordinate (ha : HasSubst a) (s : ZMod d) : subst a (s0 (K := K) s) = a (false, s) :=
  MvPowerSeries.subst_X ha _

theorem subst_first_sum_even (ha : HasSubst a) {s : ZMod d} (hs : s.val % 2 = 0) :
    subst a (s1 (K := K) s) = a (false, s) + a (true, s) := by
  unfold s1
  rw [if_pos hs, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]

theorem subst_first_odd (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s1 (K := K) s) = a (false, s) := by
  unfold s1
  rw [if_neg hs, add_zero, MvPowerSeries.subst_X ha]

theorem subst_second_even (ha : HasSubst a) {s : ZMod d} (hs : s.val % 2 = 0) :
    subst a (s2 (K := K) s) = a (true, s) := by
  unfold s2
  rw [if_pos hs, MvPowerSeries.subst_X ha]

theorem subst_second_odd (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s2 (K := K) s) = a (false, s) := by
  unfold s2
  rw [if_neg hs, MvPowerSeries.subst_X ha]

theorem subst_s1Prime_even (ha : HasSubst a) {s : ZMod d} (hs : s.val % 2 = 0) :
    subst a (s1' (K := K) s) = a (false, s) := by
  unfold s1'
  rw [if_pos hs, add_zero, MvPowerSeries.subst_X ha]

theorem subst_s1Prime_odd (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s1' (K := K) s) = a (false, s) + a (true, s) := by
  unfold s1'
  rw [if_neg hs, MvPowerSeries.subst_add ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha]

theorem subst_s2Prime_even (ha : HasSubst a) {s : ZMod d} (hs : s.val % 2 = 0) :
    subst a (s2' (K := K) s) = a (false, s) := by
  unfold s2'
  rw [if_pos hs, MvPowerSeries.subst_X ha]

theorem subst_s2Prime_odd (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s2' (K := K) s) = a (true, s) := by
  unfold s2'
  rw [if_neg hs, MvPowerSeries.subst_X ha]

end Five

section Sim

variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem simeq_sum {α : Type} (s : Finset α) (f g : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Simeq (f a) (g a)) : Simeq (∑ a ∈ s, f a) (∑ a ∈ s, g a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).1 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.2.2.1 _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem simeq_sub_zero {f g : MvPowerSeries ι K} (h : Simeq f g) : Simeq (f - g) 0 := by
  unfold Simeq at *
  rwa [sub_zero]

theorem simeq_sum_zero {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Simeq (f a) 0) : Simeq (∑ a ∈ s, f a) 0 := by
  simpa using simeq_sum s f (fun _ => 0) h

end Sim

theorem subst_letter_til (hS : SubstTil) {K : Type} [NormedField K] (l d : ℕ) [NeZero d]
    (σ : K →+* K) (hl : 2 ≤ l) (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι]
    (om oms : ι → K) (S : ZMod d → MvPowerSeries (V2 d) K) (hS0 : ∀ s, constantCoeff (S s) = 0) :
    subst (letterLog (K := K) l) (subst S (beTil l σ be0 om oms)) =
      ∑ r, subst ![linEL σ (oms r) (fun s => subst (letterLog (K := K) l) (S s)),
        linOL σ (om r) (fun s => subst (letterLog (K := K) l) (S s))] (addC l be0) := by
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hS0) hLL]
  exact hS K l d σ hl be0 ι om oms (V2 d) _
    (fun s => MvPowerSeries.constantCoeff_subst_eq_zero hLL hc (hS0 s))

end B4

open B4

theorem fourth_condition_of_pairing_rules (hP : PairRules) (hS : SubstTil) (hI : ShiftIP) (hL : LetterShift) : TorusSumCoboundaryCondition := by
  intro K _ _ _ l d _ σ hU hd hev F hF be0 hF1 ι _ om oms hO
  have hl : 2 ≤ l := hU.1.two_le
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  obtain ⟨hsh, -, -⟩ := hL K l d σ hU.1
  have ipE : ∀ (b : Bool) (r : ι),
      IP l σ (linEL σ (oms r) fun s : ZMod d => letterLog (K := K) l (b, s)) := fun b r =>
    (hI K l d σ hU hev (V2 d) _ (hsh b) (oms r) (hO.1 r).2 (hO.2 r).2).1
  have ipO : ∀ (b : Bool) (r : ι),
      IP l σ (linOL σ (om r) fun s : ZMod d => letterLog (K := K) l (b, s)) := fun b r =>
    (hI K l d σ hU hev (V2 d) _ (hsh b) (om r) (hO.1 r).1 (hO.2 r).1).2
  obtain ⟨p1, p2, -⟩ := hP K l σ hU F hF be0 hF1 (V2 d)
  constructor
  · unfold de1
    rw [MvPowerSeries.subst_sub hLL, MvPowerSeries.subst_sub hLL,
      subst_letter_til hS l d σ hl be0 ι om oms s1 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne,
      subst_letter_til hS l d σ hl be0 ι om oms s0 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero,
      subst_letter_til hS l d σ hl be0 ι om oms s2 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo,
      sub_sub, ← Finset.sum_add_distrib]
    refine simeq_sub_zero (simeq_sum _ _ _ fun r _ => ?_)
    rw [linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s) +
        letterLog (K := K) l (true, s)) (fun s hs => subst_first_sum_even hLL hs), linEL_add,
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_first_odd hLL hs),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (true, s))
        (fun s hs => subst_second_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_second_odd hLL hs)]
    exact p1 _ _ _ (ipE false r) (ipE true r) (ipO false r)
  · unfold de2
    rw [MvPowerSeries.subst_sub hLL, MvPowerSeries.subst_sub hLL,
      subst_letter_til hS l d σ hl be0 ι om oms s1' Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne',
      subst_letter_til hS l d σ hl be0 ι om oms s0 Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero,
      subst_letter_til hS l d σ hl be0 ι om oms s2' Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo',
      sub_sub, ← Finset.sum_add_distrib]
    refine simeq_sub_zero (simeq_sum _ _ _ fun r _ => ?_)
    rw [linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_s1Prime_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s) +
        letterLog (K := K) l (true, s)) (fun s hs => subst_s1Prime_odd hLL hs), linOL_add,
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s _ => subst_first_coordinate hLL s),
      linEL_congr σ (oms r) (L' := fun s => letterLog (K := K) l (false, s))
        (fun s hs => subst_s2Prime_even hLL hs),
      linOL_congr σ (om r) (L' := fun s => letterLog (K := K) l (true, s))
        (fun s hs => subst_s2Prime_odd hLL hs)]
    exact p2 _ _ _ (ipE false r) (ipO false r) (ipO true r)

namespace B4

section Linear

variable {K : Type} [Field K] {τ τ' : Type}

theorem subst_C_mul_sum {a : τ → MvPowerSeries τ' K} (ha : HasSubst a) (c : K) {α : Type}
    (s : Finset α) (f : α → MvPowerSeries τ K) :
    subst a (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, subst a (f k) := by
  rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C, ← MvPowerSeries.coe_substAlgHom ha,
    map_sum]

variable {d : ℕ} [NeZero d]

theorem first_difference_C_mul_sum (c : K) {α : Type} (s : Finset α) (f : α → MvPowerSeries (ZMod d) K) :
    de1 (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, de1 (f k) := by
  unfold de1
  rw [subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_sub, mul_sub]

theorem second_difference_C_mul_sum (c : K) {α : Type} (s : Finset α) (f : α → MvPowerSeries (ZMod d) K) :
    de2 (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, de2 (f k) := by
  unfold de2
  rw [subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne'),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo'),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_sub, mul_sub]

theorem constantCoeff_defectOne {be : MvPowerSeries (ZMod d) K} (h : constantCoeff be = 0) :
    constantCoeff (de1 be) = 0 := by
  unfold de1
  rw [map_sub, map_sub,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne)
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero)
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo)
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo h]
  simp

theorem constantCoeff_defectTwo {be : MvPowerSeries (ZMod d) K} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by
  unfold de2
  rw [map_sub, map_sub,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne')
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne' h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero)
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo')
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo' h]
  simp

theorem iterate_of_pow {σ : K →+* K} {u : K} {l : ℕ} (h : σ u = u ^ l) (j : ℕ) :
    σ^[j] u = u ^ (l ^ j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ']

end Linear

theorem exp_of_simeq {K : Type} [NormedField K] [CharZero K] {d : ℕ} [NeZero d] (l : ℕ)
    {D : MvPowerSeries (V2 d) K} (h0 : constantCoeff D = 0)
    (h : Simeq (subst (letterLog (K := K) l) D) 0) :
    Integral (subst (letterLog (K := K) l) (mvExp D)) ∧
      constantCoeff (subst (letterLog (K := K) l) (mvExp D)) = 1 := by
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hLL h0]
  unfold Simeq at h
  rw [sub_zero] at h
  exact ⟨h.2, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_mvExp' h.1⟩

end B4

theorem biextension_hypotheses_of_conditions (h4 : TorusSumCoboundaryCondition) (hT : TorusTil) (hTe : TeichSigma) (h2 : MeanTorusInvariant) (h3 : MeanNoLowBidegreeTerms) :
    MeanBiextensionHypothesesOfCocycle := by
  intro K _ _ _ l d _ σ hU hd hev F hF be0 hF1 ι _ om oms hO ζ hζ
  have hl : 2 ≤ l := hU.1.two_le
  have hld : 2 ≤ l ^ d := le_trans hl (Nat.le_self_pow (by omega) l)
  have hN0 : l ^ d - 1 ≠ 0 := by omega
  have hζ1 : ζ ^ (l ^ d - 1) = 1 := hζ.pow_eq_one
  have hu1 : ∀ k : ℕ, (ζ ^ k) ^ (l ^ d - 1) = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have huσ : ∀ k : ℕ, σ (ζ ^ k) = (ζ ^ k) ^ l := fun k =>
    hTe K l d σ hU (by omega) (ζ ^ k) (hu1 k)
  have hun : ∀ k : ℕ, ‖ζ ^ k‖ = 1 := fun k =>
    (isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ d - 1, Nat.pos_of_ne_zero hN0, hu1 k⟩).norm_eq_one
  have hu0 : ∀ k : ℕ, ζ ^ k ≠ 0 := fun k h => by
    have := hun k
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hud : ∀ k : ℕ, σ^[d] (ζ ^ k) = ζ ^ k := fun k => by
    rw [iterate_of_pow (huσ k) d]
    have : l ^ d = (l ^ d - 1) + 1 := by omega
    rw [this, pow_succ, hu1 k, one_mul]
  have hOk : ∀ k : ℕ, OwOK d σ (fun r => (ζ ^ k)⁻¹ * om r) (fun r => ζ ^ k * oms r) := by
    intro k
    refine ⟨fun r => ⟨?_, ?_⟩, fun r => ⟨?_, ?_⟩⟩
    · rw [norm_mul, norm_inv, hun k, inv_one, one_mul]
      exact (hO.1 r).1
    · rw [norm_mul, hun k, one_mul]
      exact (hO.1 r).2
    · have e := hud k
      have e' := (hO.2 r).1
      rw [← RingHom.coe_pow] at e e' ⊢
      rw [map_mul, map_inv₀, e, e']
    · have e := hud k
      have e' := (hO.2 r).2
      rw [← RingHom.coe_pow] at e e' ⊢
      rw [map_mul, e, e']
  have hmean : beMean (d := d) l σ be0 om oms ζ = MvPowerSeries.C (((l ^ d - 1 : ℕ) : K)⁻¹) *
      ∑ k ∈ Finset.range (l ^ d - 1),
        beTil l σ be0 (fun r => (ζ ^ k)⁻¹ * om r) (fun r => ζ ^ k * oms r) := by
    unfold beMean
    congr 1
    exact Finset.sum_congr rfl fun k _ => hT K l d σ hl be0 ι om oms (ζ ^ k) (hu0 k) (huσ k)
  have hb3 : NoLowBidegree (beMean (d := d) l σ be0 om oms ζ) :=
    h3 K l d σ hl hd hev be0 hF1.1 ι om oms ζ hζ
  have hcc : constantCoeff (beMean (d := d) l σ be0 om oms ζ) = 0 := by
    by_contra h
    have := (hb3 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
    simp [degE] at this
  have hc : ∀ x : V2 d, constantCoeff (letterLog (K := K) l x) = 0 :=
    Formalism.DworkPowerSeriesWeights.Transfer.cc_letterLog l
  have hLL : HasSubst (letterLog (K := K) (d := d) l) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hc
  have hndvd : ¬ l ∣ l ^ d - 1 := by
    intro h
    have h' : l ∣ l ^ d := dvd_pow_self l (by omega)
    have : l ∣ 1 := by
      have := (Nat.dvd_sub h' h)
      rwa [Nat.sub_sub_self (by omega)] at this
    have := Nat.le_of_dvd one_pos this
    omega
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K (V2 d) l σ hU.1 hU.2.2.1 hU.2.2.2.2
  refine ⟨fun n => Subfield.mem_top _, h2 K l d σ be0 ι om oms ζ hζ1, hb3, ?_, ?_⟩
  · refine exp_of_simeq l (constantCoeff_defectOne hcc) ?_
    rw [hmean, first_difference_C_mul_sum, subst_C_mul_sum hLL]
    exact hlam _ _ hndvd (simeq_sum_zero _ _ fun k _ =>
      (h4 K l d σ hU hd hev F hF be0 hF1 ι _ _ (hOk k)).1)
  · refine exp_of_simeq l (constantCoeff_defectTwo hcc) ?_
    rw [hmean, second_difference_C_mul_sum, subst_C_mul_sum hLL]
    exact hlam _ _ hndvd (simeq_sum_zero _ _ fun k _ =>
      (h4 K l d σ hU hd hev F hF be0 hF1 ι _ _ (hOk k)).2)

end Formalism.L2.Th1.D
