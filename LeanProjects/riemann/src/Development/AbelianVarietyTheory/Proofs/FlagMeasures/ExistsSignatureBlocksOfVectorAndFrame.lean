import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal

namespace GlobalTheory.SignCount

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

private theorem qEps_eq_star_dotProduct_Jm_mulVec {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    ((GlobalTheory.GaussMean.qEps ε x : ℝ) : ℂ) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  simp only [GlobalTheory.GaussMean.qEps, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]
  split_ifs <;> push_cast <;> ring

private theorem qEps_mulVec_of_conjTranspose_mul_Jm_mul {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x := by
  apply Complex.ofReal_injective
  rw [qEps_eq_star_dotProduct_Jm_mulVec, qEps_eq_star_dotProduct_Jm_mulVec, ← h, Matrix.star_mulVec]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]

private theorem qEps_not_eq_neg {m : ℕ} (ε : Fin m → Bool) (x : Fin m → ℂ) :
    GlobalTheory.GaussMean.qEps (fun a => !ε a) x = - GlobalTheory.GaussMean.qEps ε x := by
  simp only [GlobalTheory.GaussMean.qEps, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ε a = true <;> simp [h]

private theorem card_true_add_card_false_le_of_qEps_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ x, GlobalTheory.GaussMean.qEps ε (C *ᵥ x) = GlobalTheory.GaussMean.qEps η x) :
    Fintype.card {a // η a = true} + Fintype.card {a // ε a = false} ≤ m := by
  classical
  let E₁ : ({a // η a = true} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun u a => if h : η a = true then u ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : η a = true <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : η a = true <;> simp [h] }
  let E₂ : ({a // ε a = false} → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
    { toFun := fun w a => if h : ε a = false then w ⟨a, h⟩ else 0
      map_add' := by
        intro u v; funext a; by_cases h : ε a = false <;> simp [h]
      map_smul' := by
        intro c u; funext a; by_cases h : ε a = false <;> simp [h] }
  let Φ := (C.mulVecLin ∘ₗ E₁).coprod E₂
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, w⟩ hp
    have hp' : C *ᵥ E₁ u = -(E₂ w) := by
      have : C *ᵥ E₁ u + E₂ w = 0 := by simpa [Φ] using hp
      exact eq_neg_of_add_eq_zero_left this
    have hnn : ∀ a, 0 ≤ (if η a then (1 : ℝ) else -1) * ‖E₁ u a‖ ^ 2 := by
      intro a
      by_cases h : η a = true
      · simp [h]
      · simp [E₁, h]
    have hnp : GlobalTheory.GaussMean.qEps ε (-(E₂ w)) ≤ 0 := by
      unfold GlobalTheory.GaussMean.qEps
      refine Finset.sum_nonpos fun a _ => ?_
      by_cases h : ε a = false
      · simp [h]
      · simp [E₂, h]
    have hq : GlobalTheory.GaussMean.qEps η (E₁ u) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun a _ => hnn a)
      rw [← hC, hp']
      exact hnp
    have hu : u = 0 := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1 hq
      funext b
      have := hz b.1 (Finset.mem_univ _)
      simpa [E₁, b.2] using this
    have hw : w = 0 := by
      have h0 : E₂ w = 0 := by
        have : C *ᵥ E₁ u = 0 := by simp [hu]
        rw [hp'] at this
        exact neg_eq_zero.1 this
      funext b
      have := congrFun h0 b.1
      simpa [E₂, b.2] using this
    simp [hu, hw]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_prod, Module.finrank_fintype_fun_eq_card] using this

theorem card_true_eq {m : ℕ} {ε η : Fin m → Bool} (C : Matrix (Fin m) (Fin m) ℂ)
    (h : Cᴴ * Formalism.REAL.Jm ε * C = Formalism.REAL.Jm η) :
    Nat.card {a // ε a = true} = Nat.card {a // η a = true} := by
  classical
  have hC := qEps_mulVec_of_conjTranspose_mul_Jm_mul C h
  have h₁ := card_true_add_card_false_le_of_qEps_eq C hC
  have hC' : ∀ x, GlobalTheory.GaussMean.qEps (fun a => !ε a) (C *ᵥ x) =
      GlobalTheory.GaussMean.qEps (fun a => !η a) x := by
    intro x; rw [qEps_not_eq_neg, qEps_not_eq_neg, hC]
  have h₂ := card_true_add_card_false_le_of_qEps_eq C hC'
  simp only [Fintype.card_subtype] at h₁ h₂
  simp only [Bool.not_eq_true', Bool.not_eq_false'] at h₂
  have hε : (Finset.univ.filter fun a => ε a = true).card +
      (Finset.univ.filter fun a => ε a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases ε a <;> simp
    simp [this]
  have hη : (Finset.univ.filter fun a => η a = true).card +
      (Finset.univ.filter fun a => η a = false).card = m := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have : ∀ a : Fin m, ((if η a = true then 1 else 0) + (if η a = false then 1 else 0) : ℕ) = 1 := by
      intro a; cases η a <;> simp
    simp [this]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  omega

theorem card_true_cons {n : ℕ} (s : Bool) (ε' : Fin n → Bool) :
    Nat.card {a // (Fin.cons s ε' : Fin (n + 1) → Bool) a = true} =
      (if s = true then 1 else 0) + Nat.card {a // ε' a = true} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]

private theorem conjTranspose_mul_Jm_mul_apply {m : ℕ} {ι : Type*} (ε : Fin m → Bool) (M : Matrix (Fin m) ι ℂ)
    (k l : ι) :
    (Mᴴ * Formalism.REAL.Jm ε * M) k l = ∑ i, star (M i k) * ((if ε i then 1 else -1) * M i l) := by
  rw [Matrix.mul_apply]
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, mul_assoc]

theorem gram_cons {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {s : Bool}
    {x₀ : Fin (n + 1) → ℂ} {B : Matrix (Fin (n + 1)) (Fin n) ℂ}
    (h0 : GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s)
    (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ))ᴴ * Formalism.REAL.Jm ε *
      (Matrix.of fun i => (Fin.cons (x₀ i) (B i) : Fin (n + 1) → ℂ)) =
      Formalism.REAL.Jm (Fin.cons s ε') := by
  have e0 := qEps_eq_star_dotProduct_Jm_mulVec ε x₀
  rw [h0] at e0
  simp only [Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply] at e0
  have e1 : ∀ l, ∑ i, star (x₀ i) * ((if ε i then 1 else -1) * B i l) = 0 := by
    intro l
    have := congrFun h1 l
    simpa [Matrix.vecMul, dotProduct, Formalism.REAL.Jm, Matrix.diagonal_mul] using this
  ext k l
  rw [conjTranspose_mul_Jm_mul_apply]
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩ <;>
    simp only [Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
  · rw [← e0]
    cases s <;> simp [Formalism.REAL.Jm, GlobalTheory.GaussMean.sgn]
  · rw [e1]
    simp [Formalism.REAL.Jm, (Fin.succ_ne_zero l).symm]
  · have := congrArg star (e1 k)
    rw [star_sum, star_zero] at this
    rw [show (Formalism.REAL.Jm (Fin.cons s ε') : Matrix _ _ ℂ) k.succ 0 = 0 by
      simp [Formalism.REAL.Jm, Fin.succ_ne_zero k]]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp [mul_comm]
  · rw [← conjTranspose_mul_Jm_mul_apply ε B k l, h2]
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply]

theorem exists_signCompat : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  intro n ε ε' s x₀ B h0 h1 h2 P Q P' Q' f f' hf hf'
  have hc := card_true_eq _ (gram_cons h0 h1 h2)
  rw [card_true_cons, hf.card_true, hf'.card_true] at hc
  have hPQ := Sorts.add_eq f
  have hPQ' := Sorts.add_eq f'
  cases s
  · simp at hc
    let eL : Fin P' ≃ Fin P := finCongr (by omega)
    let eR : Option (Fin Q') ≃ Fin Q := (finSuccEquiv Q').symm.trans (finCongr (by omega))
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Fin P' ⊕ Option (Fin Q') :=
      { toFun := fun o => o.elim (Sum.inr none) (Sum.elim Sum.inl (fun b => Sum.inr (some b)))
        invFun := Sum.elim (fun a => some (Sum.inl a)) (fun ob => ob.map Sum.inr)
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro (_ | _ | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]
  · simp at hc
    let eL : Option (Fin P') ≃ Fin P := (finSuccEquiv P').symm.trans (finCongr (by omega))
    let eR : Fin Q' ≃ Fin Q := finCongr (by omega)
    let φ : Option (Fin P' ⊕ Fin Q') ≃ Option (Fin P') ⊕ Fin Q' :=
      { toFun := fun o => o.elim (Sum.inl none) (Sum.elim (fun a => Sum.inl (some a)) Sum.inr)
        invFun := Sum.elim (fun oa => oa.map Sum.inl) (fun b => some (Sum.inr b))
        left_inv := by rintro (_ | _ | _) <;> rfl
        right_inv := by rintro ((_ | _) | _) <;> rfl }
    refine ⟨φ.trans (Equiv.sumCongr eL eR), ?_, ?_⟩
    · intro i
      rcases i with i | i <;> simp [φ, GlobalTheory.CompactDualQuot.sg]
    · simp [φ, GlobalTheory.CompactDualQuot.sg, GlobalTheory.GaussMean.sgn]

end GlobalTheory.SignCount
