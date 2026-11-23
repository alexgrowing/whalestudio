import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.LetterShift
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries

namespace Pair

section Alg

variable {K : Type} [Field K]

private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero

theorem hs2 {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) : HasSubst ![a, b] := by
  exact hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]

theorem hs3 {τ : Type} {a b c : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (hc : constantCoeff c = 0) : HasSubst ![a, b, c] := by
  exact hasSubst_finite_of_constantCoeff_eq_zero fun i => by fin_cases i <;> first | exact ha | exact hb | exact hc | simp [ha, hb, hc]

theorem subst_subst1 {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    {a : MvPowerSeries ι K} (ha : PowerSeries.HasSubst a) (f : PowerSeries K) :
    subst b (PowerSeries.subst a f) = PowerSeries.subst (subst b a) f := by
  first
  | exact subst_comp_subst_apply (PowerSeries.HasSubst.const ha) hb f
  | exact subst_comp_subst_apply ha hb f
  | exact subst_comp_subst_apply (hasSubst_of_constantCoeff_nilpotent fun _ => ha) hb f

theorem subst_single_var {ι κ : Type} {b : ι → MvPowerSeries κ K} (hb : HasSubst b)
    (x : ι) (f : PowerSeries K) : subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [subst_subst1 hb (PowerSeries.HasSubst.of_constantCoeff_zero (a := (X x : MvPowerSeries ι K)) (by simp)) f,
    subst_X hb]

theorem constantCoeff_inVar_eq_zero {ι : Type} (x : ι) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (at1 x f) = 0 := by
  unfold at1
  exact PowerSeries.constantCoeff_subst_eq_zero (a := (X x : MvPowerSeries ι K)) (by simp) f hf

theorem subst2_comp {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    {a b : MvPowerSeries ι K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (f : MvPowerSeries (Fin 2) K) :
    subst φ (subst ![a, b] f) = subst ![subst φ a, subst φ b] f := by
  rw [subst_comp_subst_apply (hs2 ha hb) hφ]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem cc_ps {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (PowerSeries.subst a f) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem ps_comp {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) {e : PowerSeries K}
    (he : PowerSeries.constantCoeff e = 0) (f : PowerSeries K) :
    PowerSeries.subst (PowerSeries.subst a e) f = PowerSeries.subst a (PowerSeries.subst e f) := by
  have h1 : HasSubst (fun _ : Unit => a) := hasSubst_finite_of_constantCoeff_eq_zero fun _ => ha
  exact (subst_subst1 h1 (PowerSeries.HasSubst.of_constantCoeff_zero he) f).symm

theorem cc_lgF {l : ℕ} (_hl : 2 ≤ l) : PowerSeries.constantCoeff (lgF K l) = 0 := by
  first
  | simp [lgF]
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [lgF])
  | (show PowerSeries.coeff 0 (lgF K l) = 0; simp [lgF])

theorem exp_log (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) {τ : Type} {a : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a (lgF K l)) (expF K l) = a := by
  rw [ps_comp ha (cc_lgF hl) (expF K l), (hE K l hl).2.2.1]
  first
  | exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)
  | simp [PowerSeries.subst_X, PowerSeries.HasSubst.of_constantCoeff_zero ha]

theorem addC_log (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (be0 : MvPowerSeries (Fin 2) K) :
    subst ![PowerSeries.subst a (lgF K l), PowerSeries.subst b (lgF K l)] (addC l be0) =
      subst ![a, b] be0 := by
  have hA : constantCoeff (PowerSeries.subst a (lgF K l)) = 0 := cc_ps ha (cc_lgF hl)
  have hB : constantCoeff (PowerSeries.subst b (lgF K l)) = 0 := cc_ps hb (cc_lgF hl)
  have hE0 := (hE K l hl).1
  have h2 := hs2 hA hB
  unfold addC
  rw [subst_comp_subst_apply (hs2 (constantCoeff_inVar_eq_zero (0 : Fin 2) hE0) (constantCoeff_inVar_eq_zero (1 : Fin 2) hE0)) h2]
  congr 1
  funext i
  fin_cases i
  · exact (subst_single_var h2 0 (expF K l)).trans (exp_log hE hl ha)
  · exact (subst_single_var h2 1 (expF K l)).trans (exp_log hE hl hb)

private theorem mvSubst_add {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f + g) = subst φ f + subst φ g := by
  first
  | exact MvPowerSeries.subst_add hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_add _ f g)
  | exact map_add (substAlgHom hφ) f g

private theorem mvSubst_sub {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ)
    (f g : MvPowerSeries ι K) : subst φ (f - g) = subst φ f - subst φ g := by
  first
  | exact MvPowerSeries.subst_sub hφ f g
  | (rw [← coe_substAlgHom hφ]; exact map_sub _ f g)
  | exact map_sub (substAlgHom hφ) f g

theorem log_law {l : ℕ} {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0)
    (hF : cob F (lgF K l) = 0) {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    PowerSeries.subst (subst ![a, b] F) (lgF K l) =
      PowerSeries.subst a (lgF K l) + PowerSeries.subst b (lgF K l) := by
  have h2 := hs2 ha hb
  have e : PowerSeries.subst F (lgF K l) = at1 0 (lgF K l) + at1 1 (lgF K l) := by
    unfold cob at hF
    rw [sub_sub, sub_eq_zero] at hF
    exact hF
  have h := congrArg (subst ![a, b]) e
  rw [mvSubst_add h2, subst_subst1 h2 (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
    subst_single_var h2, subst_single_var h2] at h
  exact h

private theorem constantCoeff_in3_eq_zero {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by
  unfold in3
  have hx : ∀ i : Fin 2, constantCoeff (![(X 0 : MvPowerSeries (Fin 3) K), X 1] i) = 0 := by
    intro i; fin_cases i <;> simp
  first
  | exact constantCoeff_subst_eq_zero hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx hF0
  | exact constantCoeff_subst_eq_zero hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hF0 hx
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hF0 hx
  | (apply constantCoeff_subst_eq_zero <;> first | assumption | exact hasSubst_finite_of_constantCoeff_eq_zero hx)

theorem subst_first_coboundary_three {F : MvPowerSeries (Fin 2) K} (hF0 : constantCoeff F = 0) {τ : Type}
    {a b c : MvPowerSeries τ K} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0)
    (hc : constantCoeff c = 0) (H : MvPowerSeries (Fin 2) K) :
    subst ![a, b, c] (d1 F H) =
      subst ![subst ![a, b] F, c] H - subst ![a, c] H - subst ![b, c] H := by
  have h3 := hs3 ha hb hc
  have hX : ∀ i : Fin 3, constantCoeff (X i : MvPowerSeries (Fin 3) K) = 0 := fun i => by simp
  have e1 : subst ![a, b, c] (in3 F) = subst ![a, b] F := by
    unfold in3
    rw [subst2_comp h3 (hX 0) (hX 1)]
    simp only [subst_X h3]
    first | rfl | simp
  unfold d1
  rw [mvSubst_sub h3, mvSubst_sub h3, subst2_comp h3 (constantCoeff_in3_eq_zero hF0) (hX 2),
    subst2_comp h3 (hX 0) (hX 2), subst2_comp h3 (hX 1) (hX 2), e1]
  simp only [subst_X h3]
  first | rfl | simp

theorem subst_swap2 {τ : Type} {a b : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (hb : constantCoeff b = 0) (H : MvPowerSeries (Fin 2) K) :
    subst ![a, b] (swap2 H) = subst ![b, a] H := by
  have h2 := hs2 ha hb
  have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
  unfold swap2
  rw [subst2_comp h2 (hX 1) (hX 0)]
  simp only [subst_X h2]
  first | rfl | simp

def mulF (K : Type) [Field K] (l : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.subst (PowerSeries.C c * lgF K l) (expF K l)

theorem cc_C_mul_lgF {l : ℕ} (hl : 2 ≤ l) (c : K) :
    PowerSeries.constantCoeff (PowerSeries.C c * lgF K l) = 0 := by
  first
  | rw [map_mul, cc_lgF hl, mul_zero]
  | simp [cc_lgF hl]

theorem isMul_mulF (hE : ExpSpec) {l : ℕ} (hl : 2 ≤ l) (c : K) : IsMul l c (mulF K l c) := by
  refine ⟨cc_ps (τ := Unit) (cc_C_mul_lgF hl c) (hE K l hl).1, ?_⟩
  have h1 := ps_comp (τ := Unit) (a := PowerSeries.C c * lgF K l) (cc_C_mul_lgF hl c)
    (hE K l hl).1 (lgF K l)
  rw [(hE K l hl).2.1] at h1
  first
  | exact h1.trans (PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (cc_C_mul_lgF hl c)))
  | (unfold mulF; rw [h1]; simp [PowerSeries.subst_X, PowerSeries.HasSubst.of_constantCoeff_zero (cc_C_mul_lgF hl c)])

private theorem powerSeries_subst_C_mul {τ : Type} {a : MvPowerSeries τ K} (ha : constantCoeff a = 0)
    (c : K) (f : PowerSeries K) :
    PowerSeries.subst a (PowerSeries.C c * f) = C c * PowerSeries.subst a f := by
  have h := PowerSeries.HasSubst.of_constantCoeff_zero ha
  first
  | (simp only [← PowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]; exact PowerSeries.subst_smul h c f)
  | (rw [PowerSeries.subst_mul h]; congr 1; simp [PowerSeries.subst_C h])
  | (rw [← PowerSeries.coe_substAlgHom h, map_mul]; congr 1; exact (PowerSeries.substAlgHom h).commutes c)
  | simp [PowerSeries.subst_mul h]

theorem log_mul {l : ℕ} {c : K} {e : PowerSeries K} (he : IsMul l c e) {τ : Type}
    {a : MvPowerSeries τ K} (ha : constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a e) (lgF K l) =
      C c * PowerSeries.subst a (lgF K l) := by
  rw [ps_comp ha he.1 (lgF K l), he.2]
  exact powerSeries_subst_C_mul ha c (lgF K l)

theorem subst_sum {ι κ α : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) (s : Finset α)
    (f : α → MvPowerSeries ι K) : subst φ (∑ r ∈ s, f r) = ∑ r ∈ s, subst φ (f r) := by
  first
  | exact MvPowerSeries.subst_sum hφ s f
  | (rw [← coe_substAlgHom hφ]; exact map_sum _ f s)
  | exact map_sum (substAlgHom hφ) f s

theorem cc_linE {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) :
    constantCoeff (linE (d := d) σ c) = 0 := by
  unfold linE
  simp [apply_ite]

theorem cc_linO {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) :
    constantCoeff (linO (d := d) σ c) = 0 := by
  unfold linO
  simp [apply_ite]

theorem subst_zero' {ι κ : Type} {φ : ι → MvPowerSeries κ K} (hφ : HasSubst φ) :
    subst φ (0 : MvPowerSeries ι K) = 0 := by
  first
  | exact MvPowerSeries.subst_zero hφ
  | (rw [← coe_substAlgHom hφ]; exact map_zero _)
  | simp

end Alg

section NormedLin

variable {K : Type} [NormedField K]

private theorem subst_C_mul_X_eq_C_mul {ι τ : Type} {L : ι → MvPowerSeries τ K} (hL : HasSubst L) (x : K)
    (s : ι) : subst L (C x * X s) = C x * L s := by
  first
  | (simp only [← MvPowerSeries.smul_eq_C_mul]; rw [MvPowerSeries.subst_smul hL, subst_X hL])
  | (rw [← coe_substAlgHom hL, map_mul, coe_substAlgHom hL, subst_X hL]; congr 1; simp)
  | simp [subst_X hL, MvPowerSeries.subst_mul hL]

theorem subst_linE {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linE σ c) = linEL σ c L := by
  unfold linE linEL
  rw [subst_sum hL]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> first | exact subst_zero' hL | exact subst_C_mul_X_eq_C_mul hL _ s

theorem subst_linO {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linO σ c) = linOL σ c L := by
  unfold linO linOL
  rw [subst_sum hL]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> first | exact subst_zero' hL | exact subst_C_mul_X_eq_C_mul hL _ s

end NormedLin

section Normed

variable {K : Type} [NormedField K] [CharZero K]

theorem simeq_of_sub {ι : Type} {A B C : MvPowerSeries ι K} (h : Simeq (A - B - C) 0) :
    Simeq A (B + C) := by
  have e : A - (B + C) = A - B - C - 0 := by rw [sub_zero, sub_sub]
  unfold Simeq at h ⊢
  rw [e]
  exact h

end Normed

end Pair

open Pair

theorem subst_tilde : SubstTil := by
  unfold SubstTil
  intro K _ l d _ σ _hl be0 ι _ om oms τ _ L hL0
  have hL : HasSubst L := hasSubst_finite_of_constantCoeff_eq_zero hL0
  unfold beTil
  rw [subst_sum hL]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst2_comp hL (cc_linE σ (oms r)) (cc_linO σ (om r)), subst_linE σ (oms r) hL,
    subst_linO σ (om r) hL]

private theorem constantCoeff_subst_vec_pair_eq_zero {K : Type} [Field K] {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) : constantCoeff (subst ![a, b] F) = 0 := by
  have hx : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]
  first
  | exact constantCoeff_subst_eq_zero hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx hF0
  | exact constantCoeff_subst_eq_zero hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hF0 hx
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hF0 hx
  | (apply constantCoeff_subst_eq_zero <;> first | assumption | exact hasSubst_finite_of_constantCoeff_eq_zero hx)

theorem PairRules_of (hE : ExpSpec) (hIP : IPLemma) : PairRules := by
  have hS : SimeqRules := by
    first
    | exact Formalism.InvariantFactorPaths.G7.equivalence_rules
    | exact equivalence_rules
  unfold PairRules
  intro K _ _ _ l σ hU F hF be0 hF1 τ _
  obtain ⟨hF0, -, hFc⟩ := hF
  obtain ⟨-, hd, hds⟩ := hF1
  have hl : 2 ≤ l := by have := hU.2.1; omega
  have lift : ∀ G : MvPowerSeries τ K, IP l σ G → ∃ g : MvPowerSeries τ K, constantCoeff g = 0 ∧
      Integral g ∧ PowerSeries.subst g (lgF K l) = G := fun G hG => hIP K l σ hU τ G hG
  have tr : ∀ g h : MvPowerSeries τ K, constantCoeff g = 0 → constantCoeff h = 0 →
      subst ![PowerSeries.subst g (lgF K l), PowerSeries.subst h (lgF K l)] (addC l be0) =
        subst ![g, h] be0 :=
    fun g h hg hh => addC_log hE hl hg hh be0
  refine ⟨?_, ?_, ?_⟩
  · intro G G' H hG hG' hH
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨g', hg0', hgI', rfl⟩ := lift G' hG'
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    rw [← log_law hF0 hFc hg0 hg0', tr _ _ (constantCoeff_subst_vec_pair_eq_zero hg0 hg0' hF0) hh0, tr _ _ hg0 hh0,
      tr _ _ hg0' hh0]
    apply simeq_of_sub
    have h0 : ∀ i, constantCoeff (![g, g', h] i) = 0 := by
      intro i; fin_cases i <;> first | exact hg0 | exact hg0' | exact hh0
    have hI : ∀ i, Integral (![g, g', h] i) := by
      intro i; fin_cases i <;> first | exact hgI | exact hgI' | exact hhI
    have hh := (hS K (Fin 3)).2.2.2.2 τ (d1 F be0) 0 ![g, g', h] h0 hI hd
    rw [subst_first_coboundary_three hF0 hg0 hg0' hh0, subst_zero' (hs3 hg0 hg0' hh0)] at hh
    exact hh
  · intro G H H' hG hH hH'
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    obtain ⟨h', hh0', hhI', rfl⟩ := lift H' hH'
    rw [← log_law hF0 hFc hh0 hh0', tr _ _ hg0 (constantCoeff_subst_vec_pair_eq_zero hh0 hh0' hF0), tr _ _ hg0 hh0,
      tr _ _ hg0 hh0']
    apply simeq_of_sub
    have h0 : ∀ i, constantCoeff (![h, h', g] i) = 0 := by
      intro i; fin_cases i <;> first | exact hh0 | exact hh0' | exact hg0
    have hI : ∀ i, Integral (![h, h', g] i) := by
      intro i; fin_cases i <;> first | exact hhI | exact hhI' | exact hgI
    have hh := (hS K (Fin 3)).2.2.2.2 τ (d1 F (swap2 be0)) 0 ![h, h', g] h0 hI hds
    rw [subst_first_coboundary_three hF0 hh0 hh0' hg0, subst_zero' (hs3 hh0 hh0' hg0),
      subst_swap2 (constantCoeff_subst_vec_pair_eq_zero hh0 hh0' hF0) hg0, subst_swap2 hh0 hg0, subst_swap2 hh0' hg0] at hh
    exact hh
  · intro hF2 c G H hc hcc hG hH
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    have he := isMul_mulF hE hl c
    have he' := isMul_mulF hE hl (σ c)
    rw [← log_mul he hg0, ← log_mul he' hh0, tr _ _ (cc_ps hg0 he.1) hh0,
      tr _ _ hg0 (cc_ps hh0 he'.1)]
    have h0 : ∀ i, constantCoeff (![g, h] i) = 0 := by
      intro i; fin_cases i <;> first | exact hg0 | exact hh0
    have hI : ∀ i, Integral (![g, h] i) := by
      intro i; fin_cases i <;> first | exact hgI | exact hhI
    have hh := (hS K (Fin 2)).2.2.2.2 τ _ _ ![g, h] h0 hI (hF2 c hc hcc _ _ he he')
    have h2 := hs2 hg0 hh0
    have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
    rw [subst2_comp h2 (constantCoeff_inVar_eq_zero (0 : Fin 2) he.1) (hX 1), subst2_comp h2 (hX 0) (constantCoeff_inVar_eq_zero (1 : Fin 2) he'.1),
      subst_single_var h2, subst_single_var h2] at hh
    simp only [subst_X h2] at hh
    exact hh

end Formalism.L2.Th1.D
