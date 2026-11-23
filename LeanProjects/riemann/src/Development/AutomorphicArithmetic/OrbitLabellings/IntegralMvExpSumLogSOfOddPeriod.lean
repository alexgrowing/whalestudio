import Mathlib
import Development.AutomorphicArithmetic.OrbitLabellings.ColDefs
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementE
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.SingleLetterBiextensionRelation
import Formalism.GaussJetBounds.GaussJetProofs.Transfer

open UpperTheory.G2 Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual phFF thetaS NormRel)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob at1 lgF)

namespace UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

private theorem pos_add_mul {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) (a k : ℕ) :
    pos z (a + i * k) = pos z a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, ← h.add, ih, h.period]

private theorem pos_congr {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) {a b : ℕ}
    (hab : a ≡ b [MOD i]) : pos z a = pos z b := by
  rw [← Nat.mod_add_div a i, ← Nat.mod_add_div b i, pos_add_mul h, pos_add_mul h, hab]

private theorem pos_cast {Lt : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) {a b : ℕ}
    (hab : ((a : ℕ) : ZMod (2 * i)) = (b : ℕ)) : pos z a = pos z b := by
  apply pos_congr h
  rw [ZMod.natCast_eq_natCast_iff] at hab
  exact Nat.ModEq.of_mul_left 2 hab

private theorem iter_pred {Lt β : Type} {i : ℕ} {pos : Lt → ℕ → Lt} (h : IsPos i pos) (z : Lt) (b : β) (e : ℕ) :
    (fun y : Lt × β => (pos y.1 (2 * (i - 1)), y.2))^[e] (z, b) = (pos z (2 * (i - 1) * e), b) := by
  induction e with
  | zero => simp [h.zero]
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [h.add]
    congr 2

private theorem logS_eq_gLog {K Lt β : Type} [Field K] [DecidableEq Lt] [DecidableEq β] (l : ℕ) {i : ℕ} [NeZero i]
    {pos : Lt → ℕ → Lt} (h : IsPos i pos) (r : Lt) (b : β) (s : ZMod (2 * i)) :
    logS (K := K) l i pos (pos r s.val, b) =
      KernelCokernelKilling.gLog K l (fun s : ZMod (2 * i) => (pos r s.val, b)) s := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  have key : ∀ e : ℕ, pos r (s.val + 2 * (i - 1) * e) = pos r ((s - 2 * (e : ZMod (2 * i))).val) := by
    intro e
    apply pos_cast h
    have hi : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr (NeZero.ne i)
    push_cast [Nat.cast_sub hi, ZMod.natCast_zmod_val]
    have h2i : ((2 * i : ℕ) : ZMod (2 * i)) = 0 := ZMod.natCast_self _
    push_cast at h2i
    linear_combination (e : ZMod (2 * i)) * h2i
  ext n
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog, KernelCokernelKilling.gLog]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [iter_pred h, h.add, key]

private theorem val_add_i {i : ℕ} [NeZero i] (s : ZMod (2 * i)) :
    ∃ k : ℕ, s.val + i = (s + (i : ZMod (2 * i))).val + 2 * i * k := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  have hi : 0 < i := Nat.pos_of_ne_zero (NeZero.ne i)
  refine ⟨(s.val + i) / (2 * i), ?_⟩
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : i < 2 * i)]
  exact (Nat.mod_add_div _ _).symm

private theorem linOL_eq {K τ : Type} [NormedField K] {i : ℕ} [NeZero i] (hi : Odd i) (σ : K →+* K) {c : K}
    (hc : σ^[2 * i] c = c) (L : ZMod (2 * i) → MvPowerSeries τ K) (hL : ∀ s, L (s + (i : ZMod (2 * i))) = L s) :
    linOL σ c L = linEL σ (σ^[i] c) L := by
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  unfold linOL linEL
  refine Fintype.sum_equiv (Equiv.addRight (i : ZMod (2 * i))) _ _ fun s => ?_
  simp only [Equiv.coe_addRight]
  rw [hL s, ← Function.iterate_add_apply]
  obtain ⟨k, hk⟩ := val_add_i s
  obtain ⟨m, hm⟩ := hi
  have hs := ZMod.val_lt s
  have hk1 : k ≤ 1 := by
    by_contra hc'
    push_neg at hc'
    nlinarith
  have hit : σ^[(s + (i : ZMod (2 * i))).val + i] c = σ^[s.val] c := by
    interval_cases k
    · rw [show (s + (i : ZMod (2 * i))).val + i = s.val + 2 * i by omega, Function.iterate_add_apply, hc]
    · rw [show (s + (i : ZMod (2 * i))).val + i = s.val by omega]
  have hpar : s.val % 2 = 0 ↔ ¬ (s + (i : ZMod (2 * i))).val % 2 = 0 := by
    interval_cases k <;> omega
  by_cases h0 : s.val % 2 = 0
  · have h1 := hpar.mp h0
    simp [h0, h1]
  · have h1 : (s + (i : ZMod (2 * i))).val % 2 = 0 := by
      by_contra h1
      exact h0 (hpar.mpr h1)
    simp [h0, h1, hit]

private theorem diag (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l i : ℕ) [NeZero i]
    (σ : K →+* K) (hU : UnrOK K l σ) (hi : Odd i) (F : MvPowerSeries (Fin 2) K) (hF : IsLawOfLog l F)
    (be0 : MvPowerSeries (Fin 2) K) (hF1 : F1 F be0) (hF2 : F2 l σ be0) (om : Fin i → K)
    (hOw : OwOK (2 * i) σ om (fun r => σ^[i] (om r))) (hTr : TrDual (2 * i) σ om (fun r => σ^[i] (om r)))
    (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ (2 * i) - 1)) (ph : PowerSeries K)
    (hph : Simeq (C (2 : K) * ph) (subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) be0))
    (τ : Type) [Finite τ] (L : ZMod (2 * i) → MvPowerSeries τ K) (hS : ShiftType l σ L)
    (hL : ∀ s, L (s + (i : ZMod (2 * i))) = L s) :
    ∃ x : Fin i → MvPowerSeries τ K, (∀ ρ, constantCoeff (x ρ) = 0) ∧ (∀ ρ, Integral (x ρ)) ∧
      (∀ ρ, PowerSeries.subst (x ρ) (lgF K l) = linEL σ (σ^[i] (om ρ)) L) ∧
      Simeq (∑ ρ, PowerSeries.subst (x ρ) ph)
        (C ((2 : K)⁻¹) * subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)) := by
  have hlp : Nat.Prime l := hU.1
  have hl2 : 2 ≤ l := hlp.two_le
  have hd2 : 2 ≤ 2 * i := by have := NeZero.ne i; omega
  have hde : Even (2 * i) := even_two_mul i
  have hIP : ∀ ρ, IP l σ (linEL σ (σ^[i] (om ρ)) L) := fun ρ =>
    (shiftIP K l (2 * i) σ hU hde τ L hS _ (hOw.1 ρ).2 (hOw.2 ρ).2).1
  choose x hx0 hxI hxL using fun ρ => ipLemma K l σ hU τ _ (hIP ρ)
  refine ⟨x, hx0, hxI, hxL, ?_⟩
  obtain ⟨-, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ
  have hsubU := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit).2.2.2.2 τ
  have hM := meanSimeqL K l (2 * i) σ hU hd2 hde F hF be0 hF1 hF2 (Fin i) om (fun r => σ^[i] (om r))
    hOw hTr ζ hζ τ L hS
  rw [substTil K l (2 * i) σ hl2 be0 (Fin i) om _ τ L (fun s => (hS s).1)] at hM
  have ha : MvPowerSeries.HasSubst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _)
  have hterm : ∀ r : Fin i, Simeq (subst ![linEL σ (σ^[i] (om r)) L, linOL σ (om r) L] (addC l be0))
      (C (2 : K) * PowerSeries.subst (x r) ph) := by
    intro r
    rw [linOL_eq hi σ (hOw.2 r).1 L hL, ← hxL r, Pair.addC_log expSpec hl2 (hx0 r) (hx0 r) be0]
    have hb : MvPowerSeries.HasSubst (fun _ : Unit => x r) :=
      PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 r))
    have h1 := hsubU (C (2 : K) * ph) _ (fun _ => x r) (fun _ => hx0 r) (fun _ => hxI r) hph
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply ha hb] at h1
    have e : (fun _ : Fin 2 => subst (fun _ : Unit => x r) (PowerSeries.X : PowerSeries K)) = ![x r, x r] := by
      funext j
      rw [PowerSeries.X, MvPowerSeries.subst_X hb]
      fin_cases j <;> rfl
    rw [e] at h1
    exact hsymm _ _ h1
  have hsum := B4.simeq_sum Finset.univ _ _ fun r _ => hterm r
  rw [← Finset.mul_sum] at hsum
  have h2 := htrans _ _ _ hM hsum
  have hl3 : 2 < l := hU.2.1
  have hnd : ¬ l ∣ 2 := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hlam := Formalism.InvariantFactorPaths.G7.Top.lamModule K τ l σ hlp hU.2.2.1 hU.2.2.2.2 _ 2 hnd (B4.simeq_sub_zero h2)
  apply hsymm
  have key : C ((2 : K)⁻¹) * subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)
      - ∑ ρ, PowerSeries.subst (x ρ) ph
      = C ((2 : ℕ) : K)⁻¹ * (subst L (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)
        - C (2 : K) * ∑ ρ, PowerSeries.subst (x ρ) ph) := by
    rw [mul_sub, ← mul_assoc, ← map_mul, Nat.cast_ofNat, inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  unfold Formalism.InvariantFactorPaths.G7.Simeq at hlam ⊢
  rw [sub_zero] at hlam
  rw [key]
  exact hlam

private theorem map_logS {K K' Lt β : Type} [Field K] [Field K'] [DecidableEq Lt] [DecidableEq β] (j : K →+* K') (l i : ℕ)
    (pos : Lt → ℕ → Lt) (v : Lt × β) : map j (logS (K := K) l i pos v) = logS (K := K') l i pos v := by
  ext n
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog]
  simp [map_sum, apply_ite j]

private theorem cc_logS {K Lt β : Type} [Field K] [DecidableEq Lt] [DecidableEq β] {l : ℕ} (hl : 2 ≤ l) (i : ℕ)
    (pos : Lt → ℕ → Lt) (v : Lt × β) : constantCoeff (logS (K := K) l i pos v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
  simp only [logS, Formalism.DworkPowerSeriesWeights.genLog]
  simp only [map_zero, zero_add, Finset.sum_range_one, pow_zero, Function.iterate_zero, id_eq, ite_eq_right_iff]
  intro h0
  exact absurd h0.symm (Finsupp.single_ne_zero.mpr one_ne_zero)

end UpperTheory.G2.ConjugatePartitionShape

namespace UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

private theorem diagJ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (j : K0 →+* K) (hj : ∀ a, ‖j a‖ = ‖a‖) (l i : ℕ) [NeZero i]
    (σ : K0 →+* K0) (hU : UnrOK K0 l σ) (hi : Odd i) (F : MvPowerSeries (Fin 2) K0) (hF : IsLawOfLog l F)
    (be0 : MvPowerSeries (Fin 2) K0) (hF1 : F1 F be0) (hF2 : F2 l σ be0) (om : Fin i → K0)
    (hOw : OwOK (2 * i) σ om (fun r => σ^[i] (om r))) (hTr : TrDual (2 * i) σ om (fun r => σ^[i] (om r)))
    (ζ : K0) (hζ : IsPrimitiveRoot ζ (l ^ (2 * i) - 1)) (ph : PowerSeries K0)
    (hph : Simeq (C (2 : K0) * ph) (subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries K0)) be0))
    (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt) (hpos : IsPos i pos)
    (r : Lt) (b : β) :
    ∃ x : Fin i → MvPowerSeries (Lt × β) K, (∀ ρ, constantCoeff (x ρ) = 0) ∧ (∀ ρ, Integral (x ρ)) ∧
      (∀ ρ, PowerSeries.subst (x ρ) (lgF K l) =
        subst (logS (K := K) (β := β) l i pos) (linS j σ i pos (σ^[i] (om ρ)) r b)) ∧
      Simeq (∑ ρ, PowerSeries.subst (x ρ) (PowerSeries.map j ph))
        (C ((2 : K)⁻¹) * subst (fun s : ZMod (2 * i) => logS (K := K) l i pos (pos r s.val, b))
          (map j (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ))) := by
  have hlp : Nat.Prime l := hU.1
  have hl2 : 2 ≤ l := hlp.two_le
  haveI : NeZero (2 * i) := ⟨by have := NeZero.ne i; omega⟩
  set L0 : ZMod (2 * i) → MvPowerSeries (Lt × β) K0 := fun s => logS (K := K0) l i pos (pos r s.val, b) with hL0
  have hS : ShiftType l σ L0 := by
    have e : L0 = fun s => KernelCokernelKilling.gLog K0 l (fun s : ZMod (2 * i) => (pos r s.val, b)) s :=
      funext fun s => logS_eq_gLog l hpos r b s
    rw [e]
    exact KernelCokernelKilling.shiftType_gLog hlp σ _
  have hLp : ∀ s, L0 (s + (i : ZMod (2 * i))) = L0 s := by
    intro s
    obtain ⟨k, hk⟩ := val_add_i s
    have e1 : (s.val + i) % i = s.val % i := Nat.add_mod_right _ _
    have e2 : ((s + (i : ZMod (2 * i))).val + 2 * i * k) % i = (s + (i : ZMod (2 * i))).val % i := by
      rw [show 2 * i * k = i * (2 * k) by ring, Nat.add_mul_mod_self_left]
    have hmod : (s + (i : ZMod (2 * i))).val ≡ s.val [MOD i] := by
      unfold Nat.ModEq
      rw [← e2, ← hk, e1]
    simp only [hL0, pos_congr hpos r hmod]
  obtain ⟨x, hx0, hxI, hxL, hsim⟩ :=
    diag K0 l i σ hU hi F hF be0 hF1 hF2 om hOw hTr ζ hζ ph hph (Lt × β) L0 hS hLp
  have hs : MvPowerSeries.HasSubst (logS (K := K) (β := β) l i pos) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logS hl2 i pos v)
  have hs0 : MvPowerSeries.HasSubst L0 :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => cc_logS hl2 i pos _)
  refine ⟨fun ρ => map j (x ρ), fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, ?_⟩
  · rw [MvPowerSeries.constantCoeff_map, hx0, map_zero]
  · exact Formalism.DworkPowerSeriesWeights.Transfer.integral_map j hj (hxI ρ)
  · rw [← Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l,
      ← PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 ρ)), hxL ρ]
    unfold linEL linS
    rw [map_sum, Pair.subst_sum hs]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs
    · rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C,
        MvPowerSeries.subst_X hs]
      simp only [hL0, map_logS]
    · rw [map_zero, Pair.subst_zero' hs]
  · have hm := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K (Lt × β) j hj).1 _ _ hsim
    have e1 : map j (∑ ρ, PowerSeries.subst (x ρ) ph)
        = ∑ ρ, PowerSeries.subst (map j (x ρ)) (PowerSeries.map j ph) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun ρ _ =>
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (hx0 ρ)) ph
    have e2 : map j (C ((2 : K0)⁻¹) * subst L0 (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ))
        = C ((2 : K)⁻¹) * subst (fun s : ZMod (2 * i) => logS (K := K) l i pos (pos r s.val, b))
          (map j (beMean (d := 2 * i) l σ be0 om (fun r => σ^[i] (om r)) ζ)) := by
      rw [map_mul, MvPowerSeries.map_C, map_inv₀, map_ofNat, MvPowerSeries.map_subst hs0]
      congr 2
      funext s
      simp only [hL0, map_logS]
    rw [e1, e2] at hm
    exact hm

end UpperTheory.G2.ConjugatePartitionShape

open MvPowerSeries Formalism.L2.Th1.D UpperTheory.G2.ConjugatePartitionShape in
open Formalism.InvariantFactorPaths.G7 (Simeq) in
open Formalism.DworkPowerSeriesWeights (Integral mvExp) in
theorem UpperTheory.integral_mvExp_sum_logS_of_odd_period :
    ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)),
    (5 ≤ p ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS p g2 g3 ε)‖ ≤ 1) ∧
      UnrOK (MaximalUnramifiedExtension p) p σ ∧ IsLawOfLog p F ∧ ∀ α : MaximalUnramifiedExtension p, ‖α‖ = 1 → σ (σ α) = α → NormRel p σ (phFF p g2 g3 s2 ε) α) →
     ∀ (i : ℕ) [NeZero i], Odd i → ∀ om : Fin i → MaximalUnramifiedExtension p,
    OwOK (2 * i) σ om (fun r => σ^[i] (om r)) → TrDual (2 * i) σ om (fun r => σ^[i] (om r)) →
    ∀ (Lt β : Type) [Fintype Lt] [Fintype β] [DecidableEq Lt] [DecidableEq β] (pos : Lt → ℕ → Lt), IsPos i pos →
    ∀ (R : Finset Lt) (Θ : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p]),
    Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (∑ e : ({r // r ∈ R} × Fin i) × β,
              at1 e (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p]) *
      (MvPowerSeries.subst (fun e : ({r // r ∈ R} × Fin i) × β => (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ :
        MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) →
    ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (Lt × β) ℂ_[p]), ‖ep‖ = 1 →
    (MvPowerSeries.subst (fun v : Lt × β => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (Lt × β) ℂ_[p])) Th : MvPowerSeries (Lt × β) ℂ_[p]) =
      MvPowerSeries.subst (fun e : ({r // r ∈ R} × Fin i) × β => linS (MaximalUnramifiedExtension p).subtype σ i pos (σ^[i] (om e.1.2)) e.1.1.1 e.2) Θ →
    HasThetaProductForm p i pos Th := by
  intro p _ g2 g3 s2 ε σ F ⟨hp5, hg2, hg3, hε, hθ, hU, hF, hNR⟩ i _ hi om hOw hTr Lt β _ _ _ _ pos hpos R Θ hI ep Th hep hTh
  set j : ↥(MaximalUnramifiedExtension p) →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype with hjdef
  have hj : ∀ a, ‖j a‖ = ‖a‖ := FAux.norm_coe p
  have hl2 : 2 ≤ p := hU.1.two_le
  have hd2 : 2 ≤ 2 * i := by have := NeZero.ne i; omega
  have hde : Even (2 * i) := even_two_mul i
  obtain ⟨hF1, hF2, hph⟩ := FAux.ffs p first_level_on_curve g2 g3 ε hg2 hg3 hε hθ σ hU F hF s2 hNR
  have hgt : 1 < p ^ (2 * i) := Nat.one_lt_pow (by omega) (by omega)
  have hpos' : 0 < p ^ (2 * i) - 1 := by omega
  have hndvd : ¬ p ∣ p ^ (2 * i) - 1 := by
    intro hd
    have h1 : p ∣ p ^ (2 * i) := dvd_pow_self p (by omega)
    have h2 := Nat.dvd_sub h1 hd
    rw [Nat.sub_sub_self (by omega)] at h2
    have := Nat.le_of_dvd one_pos h2
    omega
  obtain ⟨ζ0, hζ0⟩ := kurRoots p (p ^ (2 * i) - 1) hpos' hndvd
  set ph := phFF p g2 g3 s2 ε with hphdef
  set be0 := cob F ph with hbe0
  set bM := beMean (d := 2 * i) p σ be0 om (fun r => σ^[i] (om r)) ζ0 with hbM
  have hB := biextension_hypotheses_of_level_one (MaximalUnramifiedExtension p) p (2 * i) σ hU hd2 hde F hF be0 hF1 (Fin i) om _ hOw ζ0 hζ0
  have hB' := (Formalism.DworkPowerSeriesWeights.admissibleTransfer (MaximalUnramifiedExtension p) ℂ_[p] j hj p (2 * i) 0 0 ⊤ ζ0 bM).2.1 hB
  have hK : Subfield.map j ⊤ = MaximalUnramifiedExtension p := by
    rw [← RingHom.fieldRange_eq_map, hjdef, Subfield.fieldRange_subtype]
  rw [hK] at hB'
  choose x hx0 hxI hxL hxS using fun (r : {r // r ∈ R}) (b : β) =>
    diagJ (MaximalUnramifiedExtension p) ℂ_[p] j hj p i σ hU hi F hF be0 hF1 hF2 om hOw hTr ζ0 hζ0 ph hph Lt β pos hpos r.1 b
  refine ⟨MaximalUnramifiedExtension p, j ζ0, R, ep, fun _ => -1, fun _ => map j bM, kurUnram p,
    hζ0.map_of_injective j.injective, hep, fun _ _ => Or.inr rfl, fun _ _ => hB', ?_⟩
  set Λ : Lt × β → MvPowerSeries (Lt × β) ℂ_[p] := logS (K := ℂ_[p]) p i pos with hΛ
  have hΛs : MvPowerSeries.HasSubst Λ :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => cc_logS hl2 i pos v)
  set y : ({r // r ∈ R} × Fin i) × β → MvPowerSeries (Lt × β) ℂ_[p] := fun e => x e.1.1 e.2 e.1.2 with hy
  have hy0 : ∀ e, constantCoeff (y e) = 0 := fun e => hx0 _ _ _
  have hyI : ∀ e, Integral (y e) := fun e => hxI _ _ _
  have hys : MvPowerSeries.HasSubst y := MvPowerSeries.hasSubst_of_constantCoeff_zero hy0
  have hat : MvPowerSeries.HasSubst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun e => Pair.constantCoeff_inVar_eq_zero e (Pair.cc_lgF hl2))
  have hlin : MvPowerSeries.HasSubst (fun e : ({r // r ∈ R} × Fin i) × β =>
      linS j σ i pos (σ^[i] (om e.1.2)) e.1.1.1 e.2) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero (fun e => ?_)
    unfold linS
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs
    · rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
    · exact map_zero _
  have hcx : MvPowerSeries.HasSubst (fun v : Lt × β => (C ep * X v : MvPowerSeries (Lt × β) ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => by simp)
  have step1 : subst (fun v => C ep * Λ v) Th = subst y (subst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ) := by
    have e1 : (fun v => C ep * Λ v) = fun v => subst Λ (C ep * X v : MvPowerSeries (Lt × β) ℂ_[p]) := by
      funext v
      rw [MvPowerSeries.subst_mul hΛs, MvPowerSeries.subst_C, MvPowerSeries.subst_X hΛs]
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hcx hΛs, hTh,
      MvPowerSeries.subst_comp_subst_apply hlin hΛs, MvPowerSeries.subst_comp_subst_apply hat hys]
    congr 1
    funext e
    rw [Pair.subst_single_var hys]
    exact (hxL _ _ _).symm
  have hph0 : PowerSeries.constantCoeff (PowerSeries.map j ph) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hphdef, FAux.cc_phFF hl2, map_zero]
  have hP0 : constantCoeff (∑ e : ({r // r ∈ R} × Fin i) × β,
      (at1 e (PowerSeries.map j ph) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => Pair.constantCoeff_inVar_eq_zero e hph0
  have hW := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' hy0 hyI hI
  rw [MvPowerSeries.subst_mul hys, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hys hP0, Pair.subst_sum hys] at hW
  simp only [Pair.subst_single_var hys] at hW
  set Q := ∑ e : ({r // r ∈ R} × Fin i) × β, PowerSeries.subst (y e) (PowerSeries.map j ph) with hQdef
  set Q2 := ∑ r : {r // r ∈ R}, ∑ b : β, C ((2 : ℂ_[p])⁻¹) *
    subst (fun s : ZMod (2 * i) => Λ (pos r.1 s.val, b)) (map j bM) with hQ2def
  have hQ : Simeq Q Q2 := by
    have eQ : Q = ∑ r : {r // r ∈ R}, ∑ b : β, ∑ ρ : Fin i,
        PowerSeries.subst (x r b ρ) (PowerSeries.map j ph) := by
      rw [hQdef, Fintype.sum_prod_type, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    rw [eQ]
    exact B4.simeq_sum _ _ _ fun r _ => B4.simeq_sum _ _ _ fun b _ => hxS r b
  set G := subst (fun e : ({r // r ∈ R} × Fin i) × β =>
      (at1 e (lgF ℂ_[p] p) : MvPowerSeries (({r // r ∈ R} × Fin i) × β) ℂ_[p])) Θ with hG
  have hbe0c : constantCoeff (map j bM) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, Formalism.DworkPowerSeriesWeights.Transfer.cc_of_noLow hB.2.2.1, map_zero]
  have hXs : ∀ (r : Lt) (b : β), MvPowerSeries.HasSubst
      (fun s : ZMod (2 * i) => (X (pos r s.val, b) : MvPowerSeries (Lt × β) ℂ_[p])) :=
    fun r b => MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => MvPowerSeries.constantCoeff_X _)
  have hbeS0 : constantCoeff (beS i pos R (fun _ => (-1 : ℂ_[p])) (fun _ => map j bM) :
      MvPowerSeries (Lt × β) ℂ_[p]) = 0 := by
    unfold beS
    rw [map_sum]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum,
      Finset.sum_eq_zero (fun b _ => MvPowerSeries.constantCoeff_subst_eq_zero (hXs r b)
        (fun s => MvPowerSeries.constantCoeff_X _) hbe0c), mul_zero]
  have hsub : subst Λ (beS i pos R (fun _ => (-1 : ℂ_[p])) (fun _ => map j bM)) = -Q2 := by
    unfold beS
    rw [Pair.subst_sum hΛs, hQ2def, ← Finset.sum_coe_sort R, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MvPowerSeries.subst_smul hΛs, Pair.subst_sum hΛs, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hXs r.1 b) hΛs]
    simp only [MvPowerSeries.subst_X hΛs]
    rw [show ((-1 : ℂ_[p]) / 2) = -(2⁻¹) by ring, map_neg, neg_mul]
  have hQc : constantCoeff Q = 0 := by
    rw [hQdef, map_sum]
    exact Finset.sum_eq_zero fun e _ => Pair.cc_ps (hy0 e) hph0
  have hQ2c : constantCoeff Q2 = 0 := by
    have := hQ.1
    rw [map_sub, hQc, zero_sub, neg_eq_zero] at this
    exact this
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (Lt × β)
  have hQ' := hsymm _ _ hQ
  refine ⟨mvExp Q * subst y G * mvExp (Q2 - Q), Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' hW hQ'.2, ?_⟩
  rw [step1, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hΛs hbeS0, hsub]
  have h1 : mvExp Q * mvExp (Q2 - Q) * mvExp (-Q2) = (1 : MvPowerSeries (Lt × β) ℂ_[p]) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hQc (by rw [map_sub, hQc, hQ2c, sub_zero]),
      ← Formalism.InvariantFactorPaths.G7.mvExp_add (by rw [map_add, map_sub, hQc, hQ2c]; simp) (by rw [map_neg, hQ2c, neg_zero])]
    rw [show Q + (Q2 - Q) + -Q2 = 0 by ring, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  calc subst y G = subst y G * (mvExp Q * mvExp (Q2 - Q) * mvExp (-Q2)) := by rw [h1, mul_one]
    _ = _ := by ring
