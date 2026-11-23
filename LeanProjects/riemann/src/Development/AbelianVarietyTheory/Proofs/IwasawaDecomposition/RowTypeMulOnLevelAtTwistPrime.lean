import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaQuotientCharMulInvEqOne

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.TwistRowMul

open GlobalTheory.TwistRowType

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_of_reduction_mul {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {a b c : E} (h : redP P c = redP P a * redP P b) : LocE.unitV ξ c = LocE.unitV ξ a * LocE.unitV ξ b := by
  unfold LocE.unitV
  by_cases hc : IsUnit (redP P c)
  · have hab := hc
    rw [h] at hab
    have ha : IsUnit (redP P a) := isUnit_of_mul_isUnit_left hab
    have hb : IsUnit (redP P b) := isUnit_of_mul_isUnit_right hab
    rw [dif_pos ha, dif_pos hb, dif_pos hc, ← Units.val_mul, ← map_mul]
    have : hc.unit = ha.unit * hb.unit := Units.ext (by simpa using h)
    rw [this]
  · rw [dif_neg hc]
    by_cases ha : IsUnit (redP P a)
    · by_cases hb : IsUnit (redP P b)
      · exact absurd (h ▸ ha.mul hb) hc
      · rw [dif_neg hb, mul_zero]
    · rw [dif_neg ha, zero_mul]

variable [StarRing E]

theorem mem_parL' (P : HeightOneSpectrum (𝓞 E)) (q kj n c : ℕ) (x : Sp E (n + c)) :
    x ∈ LocE.parL P q kj n c ↔
      ∀ i : Fin (n + c), IntAt P (((q : E) ^ (if kj ≤ i.1 ∧ i.1 < n then (1 : ℤ) else 0))⁻¹ * x i) := by
  unfold LocE.parL LocE.sclLat
  rw [Submodule.mem_comap, mem_stdAt]
  rfl

theorem block_mul' (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal) (kj n c : ℕ)
    {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ stabL E (n + c) (stdAt E (n + c) P))
    (hg' : g' ∈ stabL E (n + c) (stdAt E (n + c) P)) (hp : g ∈ stabL E (n + c) (LocE.parL P q kj n c)) :
    (redHom P).mapMatrix (blockD P kj n hg * blockD P kj n hg') =
      (redHom P).mapMatrix (blockD P kj n (mul_mem hg hg')) := by
  ext s t
  have hs0 : kj + s.1 < n := by have := s.2; omega
  have hs : kj + s.1 < n + c := by omega
  set v : Sp E (n + c) := g' (Loc.eN E (n + c) (kj + t.1)) with hv
  have hvi : ∀ i, IntAt P (v i) := (GlobalTheory.TwistRowType.mem_stdAt P _).1 ((hg' _).2 (eN_mem P _ _))
  set w : Sp E (n + c) := fun l => if kj ≤ l.1 ∧ l.1 < n then 0 else v l with hw
  have hdec : v = w + ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) • Loc.eN E (n + c) (kj + u.1) := by
    funext l
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Loc.eN, hw, smul_eq_mul]
    by_cases hl : kj ≤ l.1 ∧ l.1 < n
    · have hl2 := l.2
      rw [if_pos hl, zero_add, Finset.sum_eq_single (⟨l.1 - kj, by omega⟩ : Fin (n - kj))]
      · have e : kj + (l.1 - kj) = l.1 := by omega
        simp only [e, if_true, mul_one, Loc.atN]
        rw [dif_pos hl2]
      · intro u _ hu
        rw [if_neg, mul_zero]
        intro h
        apply hu
        apply Fin.ext
        simp only
        omega
      · simp
    · rw [if_neg hl, Finset.sum_eq_zero, add_zero]
      intro u _
      have := u.2
      rw [if_neg (by omega), mul_zero]
  have hwp : w ∈ LocE.parL P q kj n c := by
    rw [mem_parL']
    intro i
    by_cases hl : kj ≤ i.1 ∧ i.1 < n
    · simp only [hw, if_pos hl, mul_zero]
      exact (intSub P).zero_mem
    · simp only [hw, if_neg hl, zpow_zero, inv_one, one_mul]
      exact hvi i
  have hgw := (mem_parL' P q kj n c _).1 ((hp w).2 hwp) ⟨kj + s.1, hs⟩
  rw [if_pos ⟨by simp, hs0⟩, zpow_one] at hgw
  have hqE : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hqi : IntAt P (q : E) := natCast_mem (intSub P) q
  have e1 : g w ⟨kj + s.1, hs⟩ = (q : E) * ((q : E)⁻¹ * g w ⟨kj + s.1, hs⟩) := by
    rw [mul_inv_cancel_left₀ hqE]
  have hgwi : IntAt P (g w ⟨kj + s.1, hs⟩) := by rw [e1]; exact hqi.mul hgw
  have hred : redP P (g w ⟨kj + s.1, hs⟩) = 0 := by
    rw [e1, reduction_mul hqi hgw]
    have : redP P (q : E) = 0 := by
      have h := reduction_coe P (q : 𝓞 E)
      rw [map_natCast] at h
      rw [h, Ideal.Quotient.eq_zero_iff_mem]
      exact hq
    rw [this, zero_mul]
  have key : (⟨g w ⟨kj + s.1, hs⟩, hgwi⟩ : intSub P) + (blockD P kj n hg * blockD P kj n hg') s t =
      blockD P kj n (mul_mem hg hg') s t := by
    apply Subtype.ext
    have h2 : (blockD P kj n (mul_mem hg hg') s t : E) = g v ⟨kj + s.1, hs⟩ := by
      simp only [blockD, Matrix.of_apply, Loc.atN]
      rw [dif_pos hs]
      rfl
    have h1 : g v ⟨kj + s.1, hs⟩ = g w ⟨kj + s.1, hs⟩ +
        ∑ u : Fin (n - kj), Loc.atN v (kj + u.1) * g (Loc.eN E (n + c) (kj + u.1)) ⟨kj + s.1, hs⟩ := by
      conv_lhs => rw [hdec, map_add, map_sum]
      simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [h2, h1, Matrix.mul_apply, Subring.coe_add, AddSubmonoidClass.coe_finsetSum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Subring.coe_mul, mul_comm]
    congr 1
    simp only [blockD, Matrix.of_apply, Loc.atN]
    rw [dif_pos hs]
  have h3 := congrArg (redHom P) key
  rw [map_add, redHom_apply, hred, zero_add] at h3
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, h3]
  rfl

theorem lamQB_mul {K : Type} [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq0 : q ≠ 0) (hq : (q : 𝓞 E) ∈ P.asIdeal)
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n c : ℕ) {g g' : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ LocE.JQ P q kj n c) (hg' : g' ∈ LocE.JQ P q kj n c) :
    LocE.lamQB ξ kj n (g * g').toLinearMap = LocE.lamQB ξ kj n g.toLinearMap * LocE.lamQB ξ kj n g'.toLinearMap := by
  have hg1 : g ∈ stabL E (n + c) (stdAt E (n + c) P) := hg.1
  have hg2 : g' ∈ stabL E (n + c) (stdAt E (n + c) P) := hg'.1
  unfold LocE.lamQB
  rw [← mul_inv]
  congr 1
  apply isUnit_of_reduction_mul
  rw [redP_det_block P kj n hg1, redP_det_block P kj n hg2, redP_det_block P kj n (mul_mem hg1 hg2), ← Matrix.det_mul,
    ← map_mul, block_mul' P q hq0 hq kj n c hg1 hg2 hg.2]

theorem lamRow_mul : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  intro X Pr R Ch S mu sharp j P hP g hg g' hg'
  unfold Jat at hg hg'
  rw [if_neg hP] at hg hg'
  unfold lamRow
  rw [if_neg hP, if_neg hP, if_neg hP]
  exact lamQB_mul P (qOf P) (fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) (Ideal.absNorm_mem _) _ _ _ _ hg hg'

end GlobalTheory.TwistRowMul

end
