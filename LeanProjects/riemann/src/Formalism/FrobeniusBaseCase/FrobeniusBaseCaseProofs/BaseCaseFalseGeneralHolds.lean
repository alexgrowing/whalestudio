import Formalism.FrobeniusBaseCase.CoeffOfFirstMultiplier
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.SecondWayHolds

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

theorem weighted_mul_rule (k : Type*) [Field k] (Z : Type*) : MulRule k Z :=
  fun _ _ _ _ _ _ hf hg => hf.mul hg

theorem weighted_pow_rule (k : Type*) [Field k] (Z : Type*) : PowRule k Z :=
  fun _ _ _ _ N hf => hf.pow N

section general

variable {k : Type*} [Field k] {S : Type*} {v : AddValuation k (WithTop ℝ)}

def HasWtG (v : AddValuation k (WithTop ℝ)) (ω : (S →₀ ℕ) →+ ℝ) (w : ℝ)
    (f : MvPowerSeries S k) : Prop :=
  ∀ E : S →₀ ℕ, (w : WithTop ℝ) ≤ v (coeff E f) + ((ω E : ℝ) : WithTop ℝ)

theorem HasWtG.mul {ω : (S →₀ ℕ) →+ ℝ} {w1 w2 : ℝ} {f g : MvPowerSeries S k}
    (hf : HasWtG v ω w1 f) (hg : HasWtG v ω w2 g) : HasWtG v ω (w1 + w2) (f * g) := by
  intro E
  rw [le_add_coe_iff, coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  rw [v.map_mul]
  have hE : E = p.1 + p.2 := (Finset.HasAntidiagonal.mem_antidiagonal.1 hp).symm
  have : ((w1 + w2 - ω E : ℝ) : WithTop ℝ)
      = ((w1 - ω p.1 : ℝ) : WithTop ℝ) + ((w2 - ω p.2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_add, hE, map_add]; congr 1; ring
  rw [this]
  exact add_le_add ((le_add_coe_iff _ _ _).1 (hf p.1)) ((le_add_coe_iff _ _ _).1 (hg p.2))

theorem HasWtG.one {ω : (S →₀ ℕ) →+ ℝ} : HasWtG v ω 0 (1 : MvPowerSeries S k) := by
  intro E
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

theorem HasWtG.pow {ω : (S →₀ ℕ) →+ ℝ} {w : ℝ} {f : MvPowerSeries S k}
    (hf : HasWtG v ω w f) (n : ℕ) : HasWtG v ω ((n : ℝ) * w) (f ^ n) := by
  induction n with
  | zero => simpa using (HasWtG.one : HasWtG v ω 0 (1 : MvPowerSeries S k))
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring

end general

section two

variable {k : Type*} [Field k] {Z Z' : Type*} {v : AddValuation k (WithTop ℝ)}

def om2 (Z Z' : Type*) (r r' : ℝ) : ((Z ⊕ Z') →₀ ℕ) →+ ℝ where
  toFun E := (((Finsupp.sumFinsuppAddEquivProdFinsupp E).1.degree : ℕ) : ℝ) * r +
    (((Finsupp.sumFinsuppAddEquivProdFinsupp E).2.degree : ℕ) : ℝ) * r'
  map_zero' := by simp
  map_add' E F := by
    simp only [map_add, Prod.fst_add, Prod.snd_add]
    push_cast
    ring

theorem hasWt2_iff {r r' w : ℝ} {f : MvPowerSeries (Z ⊕ Z') k} :
    HasWt2 v r r' w f ↔ HasWtG v (om2 Z Z' r r') w f := by
  constructor
  · intro h E
    have h1 := h (Finsupp.sumFinsuppAddEquivProdFinsupp E).1
      (Finsupp.sumFinsuppAddEquivProdFinsupp E).2
    have h2 : Finsupp.sumElim (Finsupp.sumFinsuppAddEquivProdFinsupp E).1
        (Finsupp.sumFinsuppAddEquivProdFinsupp E).2 = E :=
      Finsupp.sumFinsuppAddEquivProdFinsupp.symm_apply_apply E
    rw [h2] at h1
    exact h1
  · intro h A B
    have h1 := h (Finsupp.sumElim A B)
    have h2 : Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B) = (A, B) :=
      Finsupp.sumFinsuppAddEquivProdFinsupp.apply_symm_apply (A, B)
    have h3 : om2 Z Z' r r' (Finsupp.sumElim A B) =
        ((A.degree : ℕ) : ℝ) * r + ((B.degree : ℕ) : ℝ) * r' := by
      show (((Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B)).1.degree : ℕ) : ℝ) * r +
        (((Finsupp.sumFinsuppAddEquivProdFinsupp (Finsupp.sumElim A B)).2.degree : ℕ) : ℝ) * r' = _
      rw [h2]
    rw [h3] at h1
    exact h1

theorem mul_rule_two_holds (k : Type*) [Field k] (Z Z' : Type*) : MulRule2 k Z Z' := by
  intro v r r' w1 w2 f g hf hg
  rw [hasWt2_iff] at *
  exact hf.mul hg

theorem pow_rule_two_holds (k : Type*) [Field k] (Z Z' : Type*) : PowRule2 k Z Z' := by
  intro v r r' w f N hf
  rw [hasWt2_iff] at *
  exact hf.pow N

end two

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

theorem coeff_zvec (d : Z) (c : C) :
    coeff (Finsupp.single d 1) (D.zvec c) = if D.ι d = c then 1 else 0 := by
  unfold zvec
  rw [map_sum, Finset.sum_eq_single d]
  · split_ifs <;> simp [coeff_X]
  · intro e _ hne
    split_ifs
    · rw [coeff_X, if_neg]
      intro h
      exact hne ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  · simp

theorem coeff_minus_one_holds : D.CoeffOfFirstMultiplier := by
  intro d b
  rw [m_succ, coeff_C_mul, map_sum]
  congr 1
  rw [Finset.sum_eq_single (D.ι d)]
  · rw [coeff_mul_C, coeff_frob_smul _ D.q_pos]
    show (coeff (Finsupp.single d 1) (D.zvec (D.ι d))) ^ D.q * _ = _
    rw [coeff_zvec, if_pos rfl, one_pow, one_mul]
  · intro c _ hne
    rw [coeff_mul_C, coeff_frob_smul _ D.q_pos]
    show (coeff (Finsupp.single d 1) (D.zvec c)) ^ D.q * _ = _
    rw [coeff_zvec, if_neg (fun h => hne h.symm), zero_pow (by have := D.q_pos; omega), zero_mul]
  · simp

theorem base_case_false_general_holds : D.BaseCaseFalseGeneral := by
  intro hK d b hb hv hW
  have h1 := hW.1 b (by rw [hb]; omega) (D.q • Finsupp.single d 1)
  rw [hb, D.zvec_eq_zero (by omega), zero_sub, map_neg, D.coeff_minus_one_holds, AddValuation.map_neg,
    AddValuation.map_mul, D.v_neg_l_inv] at h1
  have hdeg : (((D.q • Finsupp.single d 1 : Z →₀ ℕ).degree : ℕ) : ℝ) = qnum D.l := by
    rw [← D.q_cast]
    simp
  rw [hdeg] at h1
  have hqρ := D.q_rho
  induction hx : D.v (D.g (D.ι d) b) using WithTop.recTopCoe with
  | top => rw [hx] at hv; simp at hv
  | coe y =>
    rw [hx] at hv h1
    rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h1
    rw [← WithTop.coe_add, ← WithTop.coe_one, WithTop.coe_lt_coe] at hv
    simp only [top, rad] at h1
    nlinarith

theorem QSigmaSmall_statement : D.QSigmaSmall := by
  intro hK
  have h2 := D.two_K
  have hi3 : 3 ≤ D.i := by omega
  have hlR := D.lR
  have hpow : (D.l : ℝ) ^ 3 ≤ (D.l : ℝ) ^ D.i := pow_le_pow_right₀ (by linarith) hi3
  unfold qnum sg
  rw [mul_div_assoc', div_lt_one (by positivity)]
  nlinarith [sq_nonneg (D.l : ℝ)]

end Data

end

end Formalism.BaseCaseIdentities
