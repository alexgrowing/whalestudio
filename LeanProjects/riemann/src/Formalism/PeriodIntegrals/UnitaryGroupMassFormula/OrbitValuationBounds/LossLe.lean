import Formalism.SharpRestriction.Divisibility.OrbitPlaces

noncomputable section

open scoped BigOperators
open Classical
open NumberField IsDedekindDomain Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.OrbitPlaces

namespace PI.OrbBoundFW

variable {D : D7} {L : SizeData₂ D}

theorem loss_le {X : Inst D L} {E : Ent D} (hS : Shape D L X E) {C6 C : ℝ} {K : Consts} {ce : ErrC}
    (hC : CLarge C6 C K ce) {p : ℕ} [Fact p.Prime] (h : OrbOK D p) (hp : (p : ℝ) ≤ L.sc.X'' D.R.n) {i : ℕ}
    (hi : i < D.R.m) (r : Pl D) :
    C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1)) ≤
      (nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2) := by
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1]
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have ha1 : 1 < L.sc.a := hS.xa.2
  have hpa : (p : ℝ) ≤ L.sc.a := hp.trans hS.xa.1
  have hlp : 0 < Real.log p := Real.log_pos (by linarith)
  have hla : Real.log p ≤ Real.log L.sc.a := Real.log_le_log (by linarith) hpa
  have hLa : 1 ≤ Real.logb p L.sc.a := by
    rw [Real.logb, le_div_iff₀ hlp]; linarith
  have hL2 : Real.logb p (L.sc.a ^ 2) = 2 * Real.logb p L.sc.a := by
    simp only [Real.logb, Real.log_pow]; push_cast; ring
  have hL2a : Real.logb p L.sc.a ≤ Real.logb p (2 * L.sc.a) :=
    Real.logb_le_logb_of_le (by linarith) (by linarith) (by linarith)
  have hmono : ∀ j j' : ℕ, j ≤ j' → (D.R.N j : ℝ) ≤ (D.R.N j' : ℝ) := by
    intro j j' hjj
    have : D.R.N j ≤ D.R.N j' := by
      simp only [Formalism.BasicNotions.Ranks.N]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjj) _
    exact_mod_cast this
  have hNm : Nm D = (D.R.N D.R.m : ℝ) := rfl
  have hN0 : (D.R.N i : ℝ) ≤ Nm D := hNm ▸ hmono _ _ (by omega)
  have hN1 : (D.R.N (i + 1) : ℝ) ≤ Nm D := hNm ▸ hmono _ _ (by omega)
  have hk1 : (1 : ℝ) ≤ D.R.N 0 := by
    have : 1 ≤ D.R.N 0 := by
      simp only [Formalism.BasicNotions.Ranks.N]; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hNm1 : (1 : ℝ) ≤ Nm D := hk1.trans (hNm ▸ hmono _ _ (Nat.zero_le _))
  have hn2 : (2 : ℝ) ≤ nP D p := by exact_mod_cast h.two
  have hN0p : (0 : ℝ) ≤ D.R.N i := Nat.cast_nonneg _
  have hN1p : (0 : ℝ) ≤ D.R.N (i + 1) := Nat.cast_nonneg _
  have hC0 := hC.nonneg
  have hprod : (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) ≤ (nP D p : ℝ) * Nm D ^ 2 := by
    rw [mul_assoc, sq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hN0 hN1 hN1p (by linarith)) (by linarith)
  have hprod0 : 0 ≤ (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) := by positivity

  have hL4 : Real.logb p L.sc.a ≤ Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) := by
    apply Real.logb_le_logb_of_le (by linarith) (by linarith)
    have h21 : (2 : ℝ) * 1 ≤ (nP D p : ℝ) * Nm D := mul_le_mul hn2 hNm1 (by norm_num) (by linarith)
    nlinarith

  have hcl : C * (2 * Real.logb p L.sc.a + 1) ≤ (1 + K.dl1) * Real.logb p L.sc.a := by
    have e1 : C * (2 * Real.logb p L.sc.a + 1) ≤ 3 * C * Real.logb p L.sc.a := by
      nlinarith [mul_nonneg hC0 (sub_nonneg.2 hLa)]
    have e2 : 3 * C * Real.logb p L.sc.a ≤ (1 + K.dl1) * Real.logb p L.sc.a :=
      mul_le_mul_of_nonneg_right hC.dl1 (by linarith)
    linarith
  have hA : C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1)) ≤
      (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * ((1 + K.dl1) * Real.logb p L.sc.a) := by
    rw [hL2]
    have := mul_le_mul_of_nonneg_left hcl hprod0
    linarith
  have hB : (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * Real.logb p L.sc.a ≤
      (nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hprod0
  have hD : K.dl1 * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * Real.logb p L.sc.a) ≤
      K.dl1 * ((nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hprod hL2a (by linarith) (by positivity)) hC.dl1nn
  have hT2 : 0 ≤ K.dl2 * (topsOrb D p r : ℝ) * Real.logb p (2 * L.sc.a) ^ 2 := by
    have := hC.dl2; positivity
  nlinarith [hA, hB, hD, hT2]

end PI.OrbBoundFW
