import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsObjTwistBySimilitude
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TateRoot

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma isCoprime_add_sub_mul_pow_factorial {j N : ℤ} (hj : IsCoprime j N) {n : ℕ} (hn : 0 < n) :
    IsCoprime (j + (1 - j) * N ^ n.factorial) n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  apply Nat.coprime_of_dvd
  intro p hp hpν hpn
  haveI := Fact.mk hp
  have hν : ((j + (1 - j) * N ^ n.factorial : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpν
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  by_cases hN : (N : ZMod p) = 0
  · have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
    push_cast at hν
    rw [hN, zero_pow hfac, mul_zero, add_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hν
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
    have hu := hj.isUnit_of_dvd' hν hN
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  · have hdvd : p - 1 ∣ n.factorial :=
      Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)
    obtain ⟨s, hs⟩ := hdvd
    push_cast at hν
    rw [hs, pow_mul, ZMod.pow_card_sub_one_eq_one hN, one_pow] at hν
    simp at hν

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma zmod_pow_eq_pow_factorial_of_dvd {n : ℕ} (hn : 0 < n) (x : ZMod n) {c : ℕ}
    (hc : n.factorial ∣ c) (hc0 : 0 < c) : x ^ c = x ^ n.factorial := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a t : ℕ, a ≤ n → 0 < t → t ≤ n → x ^ (a + t) = x ^ a → x ^ c = x ^ n.factorial := by
    intro a t ha ht htn h
    have hstep : ∀ k, a ≤ k → x ^ (k + t) = x ^ k := by
      intro k hk
      have e1 : k + t = (k - a) + (a + t) := by omega
      have e2 : k = (k - a) + a := by omega
      rw [e1, pow_add, h, ← pow_add, ← e2]
    have hper : ∀ k s, a ≤ k → x ^ (k + t * s) = x ^ k := by
      intro k s hk
      induction s with
      | zero => simp
      | succ s ih =>
        rw [show k + t * (s + 1) = (k + t * s) + t by ring, hstep _ (by omega), ih]
    have hfac : n.factorial ≤ c := Nat.le_of_dvd hc0 hc
    have htd : t ∣ c - n.factorial :=
      Nat.dvd_sub ((Nat.dvd_factorial ht htn).trans hc) (Nat.dvd_factorial ht htn)
    obtain ⟨s, hs⟩ := htd
    have : c = n.factorial + t * s := by omega
    rw [this, hper _ _ (le_trans ha (Nat.self_le_factorial n))]
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => x ^ (i : ℕ))
    (by simp [ZMod.card])
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key a (b - a) (by omega) (by omega) (by omega)
      (by rw [show (a : ℕ) + (b - a) = b by omega]; exact heq.symm)
  · exact key b (a - b) (by omega) (by omega) (by omega)
      (by rw [show (b : ℕ) + (a - b) = a by omega]; exact heq)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in

theorem _root_.GlobalTheory.TateRoot.exists_tateIso_zeta_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (_ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) (N : ℕ) (z : k),
    0 < N → IsPrimitiveRoot z N → ∃ I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, (I'.ζ N : k) = z := by
  intro E _ _ _ H D l k _ Q _ act e I N z hN hz
  have hζ : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N := IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim N hN)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
  have hcop : IsCoprime (i : ℤ) N := by
    rw [Nat.isCoprime_iff_coprime]
    rw [← hζ.pow_iff_coprime hN, hi]
    exact hz
  suffices h : ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∃ hν : (∀ (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧
      IsCoprime (g.ν n) n), (N : ℤ) ∣ g.ν N - i by
    obtain ⟨g, hν, hg⟩ := h
    refine ⟨_root_.GlobalTheory.LevelTwist.twist I g hν, ?_⟩
    rw [_root_.GlobalTheory.LevelTwist.twist_ζ, _root_.GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, Units.val_pow_eq_pow_val, hi]
  rcases Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq
  · haveI := D.proj
    haveI := D.fin
    have hsub : Subsingleton D.La := Module.finrank_zero_iff.mp (by rw [D.rank]; exact hpq)
    let g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D :=
      { f := fun _ => LinearMap.id
        ν := fun n => i + (1 - i) * (N : ℤ) ^ n.factorial
        tower := fun n m _ _ a => ⟨0, by simp⟩
        inv := fun n _ => ⟨LinearMap.id, fun a => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
        mult := fun n _ a b => by rw [Subsingleton.elim a 0]; simp }
    refine ⟨g, fun n m hn hm => ⟨?_, isCoprime_add_sub_mul_pow_factorial hcop hn⟩, ?_⟩
    · have h := zmod_pow_eq_pow_factorial_of_dvd hn (N : ZMod n)
        (Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)) (Nat.factorial_pos _)
      have h' : (((N : ℤ) ^ n.factorial : ℤ) : ZMod n) =
          (((N : ℤ) ^ (n * m).factorial : ℤ) : ZMod n) := by
        push_cast
        exact h.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      show (n : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial)
      rw [show (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial) =
        (1 - i) * ((N : ℤ) ^ (n * m).factorial - (N : ℤ) ^ n.factorial) by ring]
      exact Dvd.dvd.mul_left h' _
    · show (N : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ N.factorial) - i
      rw [add_sub_cancel_left]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.factorial_ne_zero N)) _
  · have hgrp := _root_.GlobalTheory.SimAlg.sim_group
    obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.SimMult.exists_sim_trivial_of_mult hgrp _root_.GlobalTheory.exists_sim_lift
      E H D { l with A := 1, A_pos := Nat.one_pos } N i hN hcop (by simp)
    exact ⟨g, (hgrp E H D hpq).1 g, hg⟩

end GlobalTheory.TateRoot
