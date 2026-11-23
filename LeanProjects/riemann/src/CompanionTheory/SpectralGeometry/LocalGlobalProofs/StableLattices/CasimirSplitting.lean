import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckCasSplit

open Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (InLieHpk)

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᴴ = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.conjTranspose_apply, Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

theorem hpk_row (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    ∃ (j₀ : Fin (2 * r + k + 1)) (s : ℂ), s * s = 1 ∧ (∀ j, Formalism.QuantumDeterminants.Hpk k r i j = if j = j₀ then s else 0) ∧
      ∀ j, Formalism.QuantumDeterminants.Hpk k r j₀ j = if j = i then s else 0 := by
  have hi := i.2
  by_cases h : r ≤ i.1 ∧ i.1 ≤ r + k
  · refine ⟨i, if i.1 = r + k then -1 else 1, by split_ifs <;> simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
  · refine ⟨⟨2 * r + k - i.1, by omega⟩, 1, by simp, fun j => ?_, fun j => ?_⟩ <;>
    · have hj := j.2
      simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega

theorem hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  obtain ⟨j₀, s, hs, h1, h2⟩ := hpk_row k r i
  simp only [Matrix.mul_apply, h1, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h2,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij, hs]
  · simp [hij, Ne.symm hij]

theorem flip_facts {n : ℕ} (Hm Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Hmᴴ = Hm) (h2 : Hm * Hm = 1) :
    (Hm * Yᴴ * Hm)ᴴ * Hm = Hm * Y ∧ Hm * (Hm * Yᴴ * Hm) = Yᴴ * Hm := by
  constructor
  · simp only [Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h2,
      Matrix.mul_one]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem reH_lie (Y : Mx k r) : InLieHpk k r (reH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (reH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * reH k r Y = 0
  simp only [reH, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul, Matrix.mul_neg, h3, h4]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_add]
  abel_nf
  simp

theorem imH_lie (Y : Mx k r) : InLieHpk k r (imH k r Y) := by
  obtain ⟨h3, h4⟩ := flip_facts _ Y (hpk_herm k r) (hpk_sq k r)
  show (imH k r Y)ᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * imH k r Y = 0
  simp only [imH, sub_neg_eq_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h3, h4]
  have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
    simp
  rw [this, neg_smul, add_comm (Yᴴ * _), neg_add_cancel]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem diff_entry {F : FRep k r} (hF : F.OK) {X : Mx k r} (hX : InLieHpk k r X) (c d : F.ι) :
    HasDerivAt (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) (F.dR X c d) 0 := by
  have h1 : PI.UpqRep.inUH (PI.UpqRep.Hpk k r) 1 := by simp [PI.UpqRep.inUH]
  obtain ⟨U, G, hU, h1U, hG, hfG⟩ := hF.smooth c d 1 h1
  have hd : HasDerivAt (fun t => ex X t) X 0 := by
    simpa using hasDerivAt_mul_ex 1 X
  exact (hasDerivAt_local (A := {g | PI.UpqRep.inUH (PI.UpqRep.Hpk k r) g}) (f := fun g => F.ρ g c d)
    (ex_mem_of_lie hX) (ex_zero X) hd hU h1U hG hfG).differentiableAt.hasDerivAt

theorem dR_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) {X : Mx k r} (hX : InLieHpk k r X) :
    (F.tens F').dR X = F.dR X ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dR X := by
  ext ⟨c, c'⟩ ⟨d, d'⟩
  have h := ((diff_entry hF hX c d).mul (diff_entry hF' hX c' d')).deriv
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hF.one, hF'.one] at h
  exact h

theorem dC_tens {F F' : FRep k r} (hF : F.OK) (hF' : F'.OK) (Y : Mx k r) :
    (F.tens F').dC Y = F.dC Y ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ) + (1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC Y := by
  simp only [FRep.dC, dR_tens hF hF' (reH_lie Y), dR_tens hF hF' (imH_lie Y), Matrix.add_kronecker,
    Matrix.kronecker_add, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_add]
  abel

section Lin

set_option linter.unusedSectionVars false

variable {ι κ V : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [AddCommGroup V] [Module ℂ V]

theorem mAct_apply (A : Matrix κ ι ℂ) (x : ι → V) (c : κ) : mAct A x c = ∑ d, A c d • x d := by
  simp [mAct]

theorem mAct_add (A B : Matrix ι ι ℂ) : (mAct (A + B) : Module.End ℂ (ι → V)) = mAct A + mAct B := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [mAct_apply, add_smul, Finset.sum_add_distrib]

theorem mAct_sum {α : Type} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    (mAct (∑ a ∈ s, A a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, mAct (A a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [mAct_apply, Matrix.sum_apply, LinearMap.sum_apply, Finset.sum_apply, Finset.sum_smul]
  exact Finset.sum_comm

theorem mAct_mul (A B : Matrix ι ι ℂ) : (mAct A * mAct B : Module.End ℂ (ι → V)) = mAct (A * B) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp only [Module.End.mul_apply, mAct_apply, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem dOp_mul (S T : Module.End ℂ V) : (dOp ι (S * T) : Module.End ℂ (ι → V)) = dOp ι S * dOp ι T := rfl

theorem dOp_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ V) :
    (dOp ι (∑ a ∈ s, T a) : Module.End ℂ (ι → V)) = ∑ a ∈ s, dOp ι (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [dOp]

theorem left_factor_action_mul (f g : Module.End ℂ (ι → V)) :
    (on1 (f * g) : Module.End ℂ (ι × κ → V)) = on1 f * on1 g := rfl

theorem right_factor_action_mul (f g : Module.End ℂ (κ → V)) :
    (on2 (f * g) : Module.End ℂ (ι × κ → V)) = on2 f * on2 g := rfl

theorem left_factor_action_add (f g : Module.End ℂ (ι → V)) :
    (on1 (f + g) : Module.End ℂ (ι × κ → V)) = on1 f + on1 g := rfl

theorem right_factor_action_add (f g : Module.End ℂ (κ → V)) :
    (on2 (f + g) : Module.End ℂ (ι × κ → V)) = on2 f + on2 g := rfl

theorem left_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (ι → V)) :
    (on1 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on1 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1]

theorem right_factor_action_sum {α : Type} (s : Finset α) (T : α → Module.End ℂ (κ → V)) :
    (on2 (∑ a ∈ s, T a) : Module.End ℂ (ι × κ → V)) = ∑ a ∈ s, on2 (T a) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2]

theorem left_factor_action_diag_op (T : Module.End ℂ V) : (on1 (dOp ι T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem right_factor_action_diag_op (T : Module.End ℂ V) : (on2 (dOp κ T) : Module.End ℂ (ι × κ → V)) = dOp (ι × κ) T := rfl

theorem left_factor_action_kronecker (A : Matrix ι ι ℂ) :
    (on1 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct (A ⊗ₖ (1 : Matrix κ κ ℂ)) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on1, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem right_factor_action_kronecker (A : Matrix κ κ ℂ) :
    (on2 (mAct A) : Module.End ℂ (ι × κ → V)) = mAct ((1 : Matrix ι ι ℂ) ⊗ₖ A) := by
  refine LinearMap.ext fun x => funext fun c => ?_
  simp [on2, mAct_apply, Fintype.sum_prod_type, Matrix.one_apply, LinearMap.funLeft_apply, kroneckerMap]

theorem expand {R α : Type} [Ring R] [Fintype α] (E A B : α → α → R) (Q : R)
    (h1 : ∑ a, ∑ b, A a b * B b a = Q) (h2 : ∑ a, ∑ b, B a b * A b a = Q) :
    ∑ a, ∑ b, (E a b + (A a b + B a b)) * (E b a + (A b a + B b a)) =
      ∑ a, ∑ b, (E a b + A a b) * (E b a + A b a) + ∑ a, ∑ b, (E a b + B a b) * (E b a + B b a)
        - ∑ a, ∑ b, E a b * E b a + (Q + Q) := by
  nth_rewrite 1 [← h1]
  rw [← h2]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  abel

end Lin

theorem casSplit : CasSplit := by
  intro k r F F' U hF hF'
  simp only [cas, cas1, cas2, casR, L, left_factor_action_sum, right_factor_action_sum, left_factor_action_mul, right_factor_action_mul, left_factor_action_add, right_factor_action_add, left_factor_action_diag_op, right_factor_action_diag_op,
    left_factor_action_kronecker, right_factor_action_kronecker, dC_tens hF hF', mAct_add, dOp_sum, dOp_mul, two_smul]
  refine expand (fun a b => dOp (F.ι × F'.ι) (U.dC (Matrix.single a b 1)))
    (fun a b => mAct (F.dC (Matrix.single a b 1) ⊗ₖ (1 : Matrix F'.ι F'.ι ℂ)))
    (fun a b => mAct ((1 : Matrix F.ι F.ι ℂ) ⊗ₖ F'.dC (Matrix.single a b 1))) _ ?_ ?_
  · simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]
  · rw [Finset.sum_comm]
    simp only [mAct_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, qMat, mAct_sum]

end GlobalTheory.CompanionTheory.ZuckCasSplit

end
