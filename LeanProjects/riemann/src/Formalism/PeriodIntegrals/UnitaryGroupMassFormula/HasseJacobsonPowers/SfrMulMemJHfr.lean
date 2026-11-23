import Formalism.PeriodIntegrals.HasseJidPow
import Formalism.PeriodIntegrals.HassePresH

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.HJP

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def H (β : Idx D j N →₀ ℕ) (x : Lw X la w) : Lw X la w := hasse X la w β x

theorem H_add (β : Idx D j N →₀ ℕ) (x y : Lw X la w) : H X la w β (x + y) = H X la w β x + H X la w β y :=
  (hasse X la w β).map_add x y

theorem H_zero_right (β : Idx D j N →₀ ℕ) : H X la w β 0 = 0 :=
  (hasse X la w β).map_zero

theorem H_zero (x : Lw X la w) : H X la w 0 x = x := hasse_zero X la w x

theorem H_mul (β : Idx D j N →₀ ℕ) (x y : Lw X la w) :
    H X la w β (x * y) = ∑ q ∈ antidiagonal β, H X la w q.1 x * H X la w q.2 y :=
  hasse_mul X la w β x y

theorem sum_eq_degree (β : Idx D j N →₀ ℕ) : (β.sum fun _ n => n) = Finsupp.degree β := by
  rw [Finsupp.degree_apply]; rfl

theorem JHfr_anti (u : WeightFamilies.Wt D j) {b c : ℕ} (h : c ≤ b) : JHfr X la w u b ≤ JHfr X la w u c := by
  intro x hx
  have hx' : x ∈ JHs X la w u b := hx
  rw [← Jid_pow_smul_HK] at hx'
  have : x ∈ JHs X la w u c := by
    rw [← Jid_pow_smul_HK]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right h) hx'
  exact this

theorem mem_JHfr_zero (u : WeightFamilies.Wt D j) {x : Lw X la w} : x ∈ JHfr X la w u 0 ↔ x ∈ Hfr X la w u := by
  have e := Jid_pow_smul_HK X la w u 0
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at e
  rw [← mem_HK X la w]
  show x ∈ JHs X la w u 0 ↔ _
  rw [← e]

theorem mul_mem_JHfr {u : WeightFamilies.Wt D j} {a : ℕ} {c y : Lw X la w} (hc : c ∈ Hfr X la w (wt0 D j))
    (hy : y ∈ JHfr X la w u a) : c * y ∈ JHfr X la w u a :=
  (JHs X la w u a).smul_mem (⟨c, (mem_Frac0 X la w).2 hc⟩ : ↥(Frac0 X la w)) (show y ∈ JHs X la w u a from hy)

theorem sfr_mul_mem_JHfr {u : WeightFamilies.Wt D j} {a : ℕ} (i : Fin (WeightFamilies.dimY D j)) {y : Lw X la w}
    (hy : y ∈ JHfr X la w u a) : (sfr X la w i.succ : Lw X la w) * y ∈ JHfr X la w u (a + 1) :=
  Jid_smul_JHs_le X la w u a (Submodule.smul_mem_smul (sfr_succ_mem_Jid X la w i) (show y ∈ JHs X la w u a from hy))

theorem main (hP : PI.HassePresH) (u : WeightFamilies.Wt D j) (a : ℕ) :
    ∀ (β : Idx D j N →₀ ℕ) (x : Lw X la w), x ∈ JHfr X la w u a →
      H X la w β x ∈ JHfr X la w u (a - Finsupp.degree β) := by
  induction a with
  | zero =>
    intro β x hx
    rw [Nat.zero_sub, mem_JHfr_zero]
    exact hP X la w u β x ((mem_JHfr_zero X la w u).1 hx)
  | succ a ih =>
    intro β x hx
    have hx' : x ∈ JHs X la w u (a + 1) := hx
    rw [← Jid_pow_smul_HK, pow_succ', Submodule.mul_smul, Jid_pow_smul_HK] at hx'
    have gen : ∀ (i : Fin (WeightFamilies.dimY D j)) (m : Lw X la w), m ∈ JHfr X la w u a → ∀ β : Idx D j N →₀ ℕ,
        H X la w β ((sfr X la w i.succ : Lw X la w) * m) ∈ JHfr X la w u (a + 1 - Finsupp.degree β) := by
      intro i m hm β
      rw [H_mul]
      refine Submodule.sum_mem _ fun q hq => ?_
      have hq' : q.1 + q.2 = β := mem_antidiagonal.1 hq
      have hd : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by
        rw [← hq', map_add]
      by_cases h1 : q.1 = 0
      · have h0 : Finsupp.degree q.1 = 0 := by rw [h1, map_zero]
        rw [h1, H_zero]
        refine JHfr_anti X la w u ?_ (sfr_mul_mem_JHfr X la w i (ih q.2 m hm))
        omega
      · have h0 : Finsupp.degree q.1 ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).1 h)
        have hs : (sfr X la w i.succ : Lw X la w) ∈ Hfr X la w (wt0 D j) :=
          (mem_Frac0 X la w).1 (sfr X la w i.succ).2
        refine JHfr_anti X la w u ?_ (mul_mem_JHfr X la w (hP X la w (wt0 D j) q.1 _ hs) (ih q.2 m hm))
        omega
    have key : ∀ r ∈ Jid X la w, ∀ m ∈ JHs X la w u a, ∀ β : Idx D j N →₀ ℕ,
        H X la w β (r • m) ∈ JHfr X la w u (a + 1 - Finsupp.degree β) := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨i, rfl⟩ := hr
        intro m hm β
        exact gen i m hm β
      | zero =>
        intro m _ β
        rw [zero_smul, H_zero_right]
        exact Submodule.zero_mem _
      | add r r' _ _ h h' =>
        intro m hm β
        rw [add_smul, H_add]
        exact Submodule.add_mem _ (h m hm β) (h' m hm β)
      | smul c r _ h =>
        intro m hm β
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact h _ ((JHs X la w u a).smul_mem c hm) β
    revert β
    refine Submodule.smul_induction_on (p := fun x => ∀ β : Idx D j N →₀ ℕ,
      H X la w β x ∈ JHfr X la w u (a + 1 - Finsupp.degree β)) hx' key ?_
    intro y z hy hz β
    rw [H_add]
    exact Submodule.add_mem _ (hy β) (hz β)

theorem hasseJidPow_of (hP : PI.HassePresH) : PI.HasseJidPow := by
  intro D B P j X la N wL w u β a x hx
  have h := main X la w hP u a β x hx
  rw [← sum_eq_degree] at h
  exact h

end PI.HJP
