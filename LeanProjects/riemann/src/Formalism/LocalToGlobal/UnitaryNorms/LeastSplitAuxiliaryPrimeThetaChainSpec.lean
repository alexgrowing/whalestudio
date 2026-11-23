import Formalism.LocalToGlobal.UnitaryNorms.ArtGCut
import Formalism.LocalToGlobal.UnitaryNorms.JointCut
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.LocalRingCardinality.HostCls

noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions

variable (D : D7)

theorem condE_pos : 0 < LevelStarExponents.condE D := by
  exact AbsolutelyIrreducibleSpan.condE_pos (D := D)

theorem leastSplitAuxiliaryPrimeThetaChain_spec : (AbsolutelyIrreducibleSpan.q0 D).Prime ∧ AbsolutelyIrreducibleSpan.q0 D % (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) = 1 := by
  exact ⟨(AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).1, (AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).2.1⟩

theorem split_prime_mod_divisor_eq_one {m : ℕ} (hm : m ∣ AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D) (h2 : 2 ≤ m) : AbsolutelyIrreducibleSpan.q0 D % m = 1 := by
  have h1 := (AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).2.1
  rw [← Nat.mod_mod_of_dvd _ hm, h1]
  exact Nat.mod_eq_of_lt (by omega)

theorem q0_mod_eq_one_of_dvd_condE {m : ℕ} (hm : m ∣ LevelStarExponents.condE D) (h2 : 2 ≤ m) : AbsolutelyIrreducibleSpan.q0 D % m = 1 := by
  exact split_prime_mod_divisor_eq_one D (Dvd.dvd.mul_left hm _) h2

theorem leastSplitAuxiliaryPrime_ne_typePrimes : AbsolutelyIrreducibleSpan.q0 D ≠ D.host.pde ∧ AbsolutelyIrreducibleSpan.q0 D ≠ D.host.pde' := by
  have h1 := (AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).2.1
  have hr := (AbsolutelyIrreducibleSpan.rPr_mem (D := D)).2
  have hd : AbsolutelyIrreducibleSpan.rPr D ∣ AbsolutelyIrreducibleSpan.q0 D - 1 := by
    have h := Nat.div_add_mod (AbsolutelyIrreducibleSpan.q0 D) (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)
    rw [h1] at h
    have e : AbsolutelyIrreducibleSpan.q0 D - 1 = AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D * (AbsolutelyIrreducibleSpan.q0 D / (AbsolutelyIrreducibleSpan.rPr D * LevelStarExponents.condE D)) := by
      omega
    rw [e, mul_assoc]
    exact dvd_mul_right _ _
  constructor
  · intro he
    rw [he] at hd
    exact hr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _) _)
  · intro he
    rw [he] at hd
    exact hr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)

theorem q0_ne_two_and_ne_q_and_ne_d : AbsolutelyIrreducibleSpan.q0 D ≠ 2 ∧ AbsolutelyIrreducibleSpan.q0 D ≠ D.host.q ∧ AbsolutelyIrreducibleSpan.q0 D ≠ D.host.d := by
  have hb := D.host.qd_big
  have hq : D.host.q ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hd : D.host.d ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_left _ _
  have mq := q0_mod_eq_one_of_dvd_condE D hq (by omega)
  have md := q0_mod_eq_one_of_dvd_condE D hd (by omega)
  have h2 := AbsolutelyIrreducibleSpan.auxiliary_prime_odd D
  refine ⟨fun h => by rw [h] at h2; norm_num at h2, fun h => ?_, fun h => ?_⟩
  · rw [h, Nat.mod_self] at mq
    exact absurd mq (by norm_num)
  · rw [h, Nat.mod_self] at md
    exact absurd md (by norm_num)

theorem split_prime_jacobi_of_three_mod_four {m : ℕ} (hm : m.Prime) (hm4 : m % 4 = 3) (hdv : m ∣ LevelStarExponents.condE D) :
    jacobiSym (-(m : ℤ)) (AbsolutelyIrreducibleSpan.q0 D) = 1 := by
  have hm2 : 2 ≤ m := hm.two_le
  have hq := q0_mod_eq_one_of_dvd_condE D hdv hm2
  have hq0 := (AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).1
  have h2 : AbsolutelyIrreducibleSpan.q0 D ≠ 2 := (q0_ne_two_and_ne_q_and_ne_d D).1
  have hv : ((1 : (ZMod m)ˣ) : ZMod m) = (AbsolutelyIrreducibleSpan.q0 D : ZMod m) := by
    rw [Units.val_one, ← ZMod.natCast_mod (AbsolutelyIrreducibleSpan.q0 D) m, hq, Nat.cast_one]
  rw [← sqSign_eq_jacobi hm hq0 hm4 h2 1 hv]
  simp [sqSign]

theorem split_prime_jacobi_neg_d : jacobiSym (-(D.host.d : ℤ)) (AbsolutelyIrreducibleSpan.q0 D) = 1 := by
  have hh := D.host.hyp
  have h16 := hh.2.2.2.1
  exact split_prime_jacobi_of_three_mod_four D hh.2.1 (by omega) (by
    unfold LevelStarExponents.condE
    exact dvd_mul_left _ _)

theorem split_prime_mod_conductor_eq_one : AbsolutelyIrreducibleSpan.q0 D % D.host.condN = 1 := by
  have hh := D.host.hyp
  have hq2 := hh.1.two_le
  have hdv : D.host.q ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have h2 : 2 ≤ LevelStarExponents.condE D := le_trans hq2 (Nat.le_of_dvd (condE_pos D) hdv)
  exact q0_mod_eq_one_of_dvd_condE D dvd_rfl h2

theorem split_prime_splits_completely : (placesOver D.host.E (AbsolutelyIrreducibleSpan.q0 D)).ncard = Module.finrank ℚ D.host.E := by
  haveI : Fact (AbsolutelyIrreducibleSpan.q0 D).Prime := ⟨(AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).1⟩
  exact Formalism.BasicNotions.Examples₂.placesOver_ncard_of_split (hpm := split_prime_mod_conductor_eq_one D) ..

variable {D}

def underQ (D : D7) (nch : NChoice D) : Set ℕ :=
  {p | p.Prime ∧ ∃ w, D.what₂.muAt w ≠ D.what₂.mu0 ∧ ∃ v ∈ nch.Q w, v ∈ placesOver D.host.E p}

structure LevelTied (D : D7) : Prop where
  eq : ∀ p, p ∈ D.host.levelPrimes ↔
    (∃ i, p = D.host.g i) ∨ p = D.host.pde ∨ p = D.host.pde' ∨ (∃ u, p = (D.mem u).A.T) ∨ p = AbsolutelyIrreducibleSpan.q0 D

theorem LevelTied.prime (h : LevelTied D) : ∀ p ∈ D.host.levelPrimes, p.Prime := by
  intro p hp
  rcases (h.eq p).mp hp with ⟨i, rfl⟩ | rfl | rfl | ⟨u, rfl⟩ | rfl
  · exact D.host.g_prime i
  · exact D.host.pde_prime
  · exact D.host.pde'_prime
  · exact (D.mem u).A.T_prime
  · exact (AbsolutelyIrreducibleSpan.auxiliary_prime_mem (D := D)).1

theorem LevelTied.auxiliary_prime_mem (h : LevelTied D) : AbsolutelyIrreducibleSpan.q0 D ∈ D.host.levelPrimes := by
  exact (h.eq _).mpr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

end Formalism.L2.Host
