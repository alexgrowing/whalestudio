import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.LieAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zero_of_constantCoeff {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) f = 0 := by
  have ha : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  by_cases h : a = 0
  · subst h
    rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h
    have : (a.prod fun _ k => (0 : MvPowerSeries (Fin d) R) ^ k) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 (by simpa using hs))
        (zero_pow (by simpa using hs))
    rw [this, map_zero, smul_zero]

theorem constantCoeff_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem subst_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf0 : constantCoeff f = 0)
    (hf : cob1 μ f = 0) (n : ℕ) : subst (nmul μ n) f = (n : R) • f := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul]
    exact subst_zero_of_constantCoeff hf0
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    have hb := hasSubst_of_constantCoeff_zero hs
    have hm : nmul μ (n + 1) = fun i => subst (Sum.elim (nmul μ n) fun i => X i) (μ i) := by
      rw [nmul, Function.iterate_succ_apply', ← nmul]; rfl
    have hc : subst μ f = inL f + inR f := by
      rw [cob1, sub_sub, sub_eq_zero] at hf; exact hf
    have hl0 : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    have hr0 : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    rw [hm, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hb, hc,
      subst_add hb, inL, inR,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hl0) hb,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr0) hb]
    simp only [subst_X hb, Sum.elim_inl, Sum.elim_inr]
    rw [ih, subst_self, id, Nat.cast_succ, add_smul, one_smul]

theorem nmul_succ {S : Type} [CommRing S] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  rw [nmul, Function.iterate_succ_apply', ← nmul]

theorem up_nmul {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ n) = nmul (up Q μ) n := by
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    funext i
    rw [nmul_succ, nmul_succ, ← ih]
    simp only [up, op, at2]
    rw [map_subst (hasSubst_of_constantCoeff_zero hs)]
    congr 1
    funext j
    rcases j with j | j <;> simp [map_X, up]

end GlobalTheory.QLog.LieAdd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem Chart.isLie_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C),
    constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c f hf0 hf
  have hμ := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    rw [up, constantCoeff_map, hμ, map_zero]
  refine (c.isLie_iff hv.hom_inj f 0).2 fun n => ⟨0, ?_, fun w φ _ => by simp⟩
  rw [map_zero, defect, LieAdd.up_nmul hμ, LieAdd.subst_nmul hμC hf0 hf, sub_self]

end GlobalTheory.QLog
