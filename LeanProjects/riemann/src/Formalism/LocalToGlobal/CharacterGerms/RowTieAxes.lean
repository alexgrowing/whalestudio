import Formalism.LocalToGlobal.CharacterGerms.RowTieFB

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section VanS

variable {τ : Type}

def Van (T : Set τ) (f : MvPowerSeries τ C) : Prop :=
  ∀ ν : τ →₀ ℕ, (∀ w ∈ ν.support, w ∉ T) → coeff ν f = 0

theorem Van.mul_right {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) :
    Van T (f * g) := by
  intro ν hν
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have h0 : coeff a f = 0 := hf a fun w hw => hν w (by
    rw [← hab', Finsupp.mem_support_iff, Finsupp.add_apply]
    have := Finsupp.mem_support_iff.1 hw
    omega)
  simp [h0]

theorem Van.const {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) : constantCoeff f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact hf 0 (by simp)

theorem Van.smul {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (c : C) : Van T (c • f) := by
  intro ν hν
  rw [coeff_smul, hf ν hν, mul_zero]

theorem Van.subst {σ : Type} [Finite σ] {T : Set τ} (S : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s ∈ S, Van T (a s)) {f : MvPowerSeries σ C}
    (hf : ∀ e : σ →₀ ℕ, (∀ s ∈ e.support, s ∉ S) → coeff e f = 0) : Van T (MvPowerSeries.subst a f) := by
  intro ν hν
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases h : ∀ s ∈ e.support, s ∉ S
  · rw [hf e h, zero_smul]
  · push Not at h
    obtain ⟨s, hs, hsS⟩ := h
    have hv : Van T (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs]
      apply Van.mul_right
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
      show Van T (a s ^ e s)
      rw [hm, pow_succ']
      exact (haS s hsS).mul_right _
    rw [hv ν hν, smul_zero]

end VanS

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem van_lin (g : Fin 2) (b : I g → C) :
    Van {w : WV I | w.1 = g} (∑ c : I g, b c • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) := by
  intro ν hν
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [coeff_smul, coeff_X, if_neg, mul_zero]
  intro h
  exact hν ⟨g, c⟩ (by rw [h]; simp) rfl

theorem van_expPt (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2) (x : κ) :
    Van {w : WV I | w.1 = g} (X.expPt g x) := by
  unfold expPt
  refine Van.subst Set.univ (fun i => (van_lin g _).const) (fun i _ => van_lin g _) ?_
  intro e he
  have he0 : e = 0 := by
    rw [← Finsupp.support_eq_empty]
    exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
  rw [he0, coeff_zero_eq_constantCoeff_apply]
  exact hex x

theorem van_hRow (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) :
    Van {w : WV I | w.1 = g} X.hRow := by
  unfold hRow
  apply Van.smul
  refine Van.subst {s : Fin 2 × κ | s.1 = g} (fun s => (X.van_expPt hex s.1 s.2).const) ?_ hh
  rintro ⟨g', x⟩ hs
  have hg : g' = g := hs
  subst hg
  exact X.van_expPt hex g' x

theorem axes_of (hex : ∀ x, constantCoeff (X.ex x) = 0)
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) : X.AxesSt := by
  intro μ h
  rcases h with h | h
  · exact X.van_hRow hex 1 (hh 1) μ fun w hw hw1 => by
      have h0 := h w hw
      have h1 : w.1 = 1 := hw1
      rw [h0] at h1
      exact absurd h1 (by decide)
  · exact X.van_hRow hex 0 (hh 0) μ fun w hw hw0 => by
      have h1 := h w hw
      have h0 : w.1 = 0 := hw0
      rw [h1] at h0
      exact absurd h0 (by decide)

end RawChart

section FBpart

variable {dd : ℕ}

theorem fin_two_eq_one_sub_of_ne' : ∀ g g' : Fin 2, g' ≠ g → g' = 1 - g := by decide

theorem coeff_of_ev_zero (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) (hz : ev a h = 0) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0 := by
  intro e he
  set b : Fin 1 × Fin dd → PS C 2 dd := fun q => X (1 - g, q.2) with hb
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero fun q => constantCoeff_X _
  have haS : HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact constantCoeff_X _
  have key : MvPowerSeries.subst b (ev a h) =
      rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
    unfold ev
    rw [subst_comp_subst_apply haS hbS, rescale_eq_subst]
    congr 1
    funext s
    by_cases hs : s.1 = g
    · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
      rw [h1, ← coe_substAlgHom hbS, map_zero]
      simp [hs]
    · have h1 : a s.1 s.2 = X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
      rw [h1, subst_X hbS]
      have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
      simp only [Pi.smul_apply', if_neg hs, one_smul, hb]
      rw [← h2]
  have h3 := congrArg (coeff e) key
  rw [hz, ← coe_substAlgHom hbS, map_zero, map_zero, coeff_rescale] at h3
  have h4 : (e.prod fun s m => (if s.1 = g then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    show (if s.1 = g then (0 : C) else 1) ^ e s = 1
    rw [if_neg (he s hs), one_pow]
  rw [h4, one_mul] at h3
  exact h3.symm

theorem constantCoeff_uncurry (f : PS C 1 dd) : constantCoeff (un1 f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  show coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = coeff 0 f
  rw [Finsupp.mapDomain_zero]

theorem axesFB : AxesFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (un1 (Y.ex x)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const x
  · intro g
    show ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end FBpart

end Formalism.L2.FormalSeriesBounds
