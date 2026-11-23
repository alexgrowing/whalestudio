import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependenceStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.TwistCoset

theorem tx_eq_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  refine Eq.trans (tsum_congr fun χ => ?_) ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)
  exact (GlobalTheory.T.thetaConstantTerm_representative_dependence O N m hm p p' χ).1 z h1 h2

variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {l : ℕ}

theorem twRel_mul {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a') (hb : TwRel β u r b b') :
    TwRel β u r (a * b) (a' * b') := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨congrArg₂ (fun s t : Multiplicative N.X => s * t) a1 b1,
    congrArg₂ (fun s t : N.A => s * t) a2 b2, fun z => ?_⟩
  change a'.1.2.s z * b'.1.2.s z / N.θ (N.c z) a'.1.2.b b'.1.2.b =
    a.1.2.s z * b.1.2.s z / N.θ (N.c z) a.1.2.b b.1.2.b * r ^ β.be (a.1.1.toAdd + b.1.1.toAdd) z
  rw [a2, b2, a3, b3, map_add, LinearMap.add_apply, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twRel_qEq (hr : r ^ l = u) {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a')
    (hb : TwRel β u r b b') (h : N.QEq a b) : (N.twist β u).QEq a' b' := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (w : N.X) => ?_)⟩
  · rw [a1, b1]; exact h1
  · refine b2.trans ?_
    rw [h2]
    exact congrArg (fun s : N.A => s * N.c z) a2.symm
  · change b'.1.2.s w = a'.1.2.s w * (N.twist β u).τ z w / N.θ (N.c w) a'.1.2.b (N.c z)
    have e : r ^ ((l : ℤ) * β.be z w) = u ^ β.be z w := by rw [zpow_mul, zpow_natCast, hr]
    rw [b3, a3, a2, N.twist_τ, h1, h2, NumD.Gt.mul_s, NumD.io_s, NumD.io_b, map_add, LinearMap.add_apply, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul, zpow_add, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]; abel

theorem exists_twRel_of_eq_one (r : Oˣ) (h : (N.twist β u).QT l) (h1 : h.1.1 = 1) {e : ℕ} (he : h.1.2 ^ e = 1) :
    ∃ h₀ : N.QT l, h₀ ^ e = 1 ∧ TwRel β u r h₀ h := by
  let f : (N.twist β u).Gt →* N.Gt := MonoidHom.mk' (fun g => ⟨g.b, g.s, g.mult⟩) fun _ _ => rfl
  have hl : h.1.2 ^ l = 1 := by
    rw [(N.twist β u).mem_QT.1 h.2, h1]; exact (N.twist β u).io_zero
  refine ⟨⟨(1, f h.1.2), ?_⟩, Subtype.ext (Prod.ext (one_pow e) ?_), h1, rfl, fun z => ?_⟩
  · rw [NumD.mem_QT, ← map_pow, hl, map_one]; exact N.io_zero.symm
  · change f h.1.2 ^ e = 1
    rw [← map_pow, he, map_one]
  · change h.1.2.s z = h.1.2.s z * r ^ β.be 0 z
    rw [map_zero, LinearMap.zero_apply, zpow_zero, mul_one]

variable {La : Type} [AddCommGroup La] {q : La → N.QT l}

theorem qEq_zero (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) : N.QEq (q 0) 1 := by
  have := TateInh.qEq_mul N (hq 0 0) ((N.qEq_equivalence l).refl (q 0)⁻¹)
  rwa [add_zero, mul_inv_cancel_right, mul_inv_cancel] at this

theorem qEq_nsmul (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (a : La) (e : ℕ) : N.QEq (q a ^ e) (q (e • a)) := by
  have E := N.qEq_equivalence l
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact E.symm (qEq_zero hq)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact E.trans (TateInh.qEq_mul N ih (E.refl _)) (hq _ _)

theorem qEq_pow {a b : N.QT l} (h : N.QEq a b) (e : ℕ) : N.QEq (a ^ e) (b ^ e) := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact (N.qEq_equivalence l).refl _
  | succ e ih => rw [pow_succ, pow_succ]; exact TateInh.qEq_mul N ih h

theorem eq_zero_of_pow_nsmul {n : ℕ} (hn : ∀ a : La, n • a = 0 → a = 0) (e : ℕ) (a : La) (h : n ^ e • a = 0) :
    a = 0 := by
  induction e with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih => exact ih (hn _ (by rwa [pow_succ', mul_smul] at h))

end GlobalTheory.TwistCoset

open GlobalTheory.TwistCoset in

theorem GlobalTheory.twist_tx_coset_norm_ge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  intro C _ _ _ _ N k β u r qf n g j hp ho hn hj hu hr hI hqf hT La _ q htf hadd hker honto p hpq
  have hm : Odd (n ^ j) := ho.pow
  have E := N.qEq_equivalence ((n ^ j) ^ 2)
  have hP : qf.PosDef := GlobalTheory.CosetCrit.posDef_of_tendsto (X := N.X) hI.pos
  have key : ∀ (x : La) (χ₀ : N.X), (∀ χ : N.X, qf ((q x).1.1.toAdd + n ^ j • χ₀) ≤ qf ((q x).1.1.toAdd + n ^ j • χ)) →
      ∃ e, Real.exp (-(qf ((q x).1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤
        ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • e))‖ := fun x χ₀ h₀ => by
    obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge (N := N.twist β u) (q := qf) hI hp ho hn hT hj (p x)
      (χ₀ := χ₀) (by rw [(hpq x).1]; exact h₀)
    obtain ⟨h', h4, h5⟩ := exists_twRel_of_eq_one r h h1 h2
    obtain ⟨a, ha⟩ := honto h'
    have h6 : N.QEq (q (n ^ (j + 1) • a)) (q 0) := by
      have := qEq_pow ha (n ^ (j + 1))
      rw [h4] at this
      exact E.trans (E.symm (qEq_nsmul hadd a _)) (E.trans this (E.symm (qEq_zero hadd)))
    obtain ⟨e, he⟩ := (hker _ _).1 h6
    have h7 : a = n ^ (j - 1) • e := by
      refine sub_eq_zero.1 (eq_zero_of_pow_nsmul htf (j + 1) _ ?_)
      rw [smul_sub, he, zero_add, ← mul_smul, ← pow_add, ← pow_mul, show j + 1 + (j - 1) = j * 2 by omega, sub_self]
    refine ⟨e, ?_⟩
    have h8 : N.QEq (q x * h') (q (x + a)) := E.trans (TateInh.qEq_mul N (E.refl _) (E.symm ha)) (hadd x a)
    rw [← h7, tx_eq_of_qEq _ hm (twRel_qEq hr (twRel_mul (hpq x) h5) (hpq (x + a)) h8)]
    rw [(hpq x).1] at h3
    exact h3
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨z, hz, -⟩ := E.symm (qEq_zero hadd)
    have hz0 : (q 0).1.1.toAdd + n ^ j • (-(n ^ j • z)) = 0 := by
      rw [hz, smul_neg, ← mul_smul, ← sq]
      exact (congrArg (· + -((n ^ j) ^ 2 • z)) (zero_add _)).trans (add_neg_cancel _)
    obtain ⟨e, he⟩ := key 0 (-(n ^ j • z)) fun χ => by rw [hz0, map_zero]; exact hP.nonneg _
    rw [hz0, map_zero, zero_div, neg_zero, Real.exp_zero] at he
    exact ⟨_, he⟩
  · obtain ⟨χ₀, h₀⟩ := (GlobalTheory.CosetCrit.tendsto_class (X := N.X) (q := qf) hI.pos (q x).1.1.toAdd
      hm.pos.ne').exists_forall_le
    obtain ⟨e, he⟩ := key x χ₀ h₀
    refine ⟨e, le_trans ?_ he⟩
    have h1 := h₀ 0
    rw [smul_zero, add_zero, hqf (q x).1.1.toAdd] at h1
    have h2 := hP.nonneg ((q x).1.1.toAdd + n ^ j • χ₀)
    set y := (q x).1.1.toAdd
    have hB : 0 ≤ β.be y y := by
      by_cases hy : y = 0
      · rw [hy, map_zero]
      · exact (β.pos y hy).le
    have h0 : 0 < ‖(u : C)‖ := norm_pos_iff.2 u.ne_zero
    have hL : Real.log ‖(u : C)‖ < 0 := Real.log_neg h0 hu
    have hc : (((β.be y y).toNat : ℕ) : ℝ) = (β.be y y : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hB]
    have hB' : (0 : ℝ) ≤ (β.be y y : ℝ) := by exact_mod_cast hB
    have hsq : (1 : ℝ) ≤ ((n ^ j : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm.pos)
    have h3 := div_le_self h2 hsq
    rw [← Real.exp_log (pow_pos h0 _), Real.log_pow, hc]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hB' (neg_pos.2 hL).le]
