import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.InstDefs

noncomputable section

open MeasureTheory NumberField Matrix
open scoped ENNReal Pointwise

namespace PI.ScMuExists.UnitaryGroupMassFormula

theorem inst_mem_frameSet {I : Formalism.MainNotions.S.AutInst} {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (j : Fin r ⊕ Fin r ⊕ Unit) : instFvec e f z j ∈ frameSet I e f z := by
  rcases j with a | a | u <;> simp [instFvec, frameSet]

theorem inst_col {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (j : Fin r ⊕ Fin r ⊕ Unit) :
    instBmat I v e f z *ᵥ Pi.single j 1 = rv I v (instFvec e f z j) := by
  ext i
  rw [Matrix.mulVec_single_one]
  simp [instBmat]

theorem inst_fix_of {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ) (hm : m * instBmat I v e f z = instBmat I v e f z) :
    ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x := by
  intro x hx
  obtain ⟨j, rfl⟩ : ∃ j, instFvec e f z j = x := by
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr (Sum.inl a), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ()), (Set.mem_singleton_iff.1 hx).symm⟩
  rw [← inst_col v e f z j, Matrix.mulVec_mulVec, hm]

theorem inst_fixB_of {I : Formalism.MainNotions.S.AutInst} (v : InfinitePlace I.F) {r : ℕ} (e f : Fin r → Fin I.n → I.E)
    (z : Fin I.n → I.E) (m : Matrix (Fin I.n) (Fin I.n) ℂ)
    (hm : ∀ x ∈ frameSet I e f z, m *ᵥ rv I v x = rv I v x) : m * instBmat I v e f z = instBmat I v e f z := by
  have hcol : ∀ j, (m * instBmat I v e f z) *ᵥ Pi.single j 1 = instBmat I v e f z *ᵥ Pi.single j 1 := by
    intro j
    rw [← Matrix.mulVec_mulVec, inst_col v e f z j, hm _ (inst_mem_frameSet e f z j)]
  ext i j
  have h := congrFun (hcol j) i
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem instDecomp_of (hP : InstPlaceDecomp) (hG : InstFrameGram) : InstDecomp := by
  intro I r e f z hF h hh
  have key := fun v : InfinitePlace I.F =>
    hP I.n (I.ε v) (Fin r ⊕ Fin r ⊕ Unit) (instBmat I v e f z) (hG I r e f z hF v)
      (Formalism.MainNotions.S.uMat (h v)) (h v).2 (inst_fixB_of v e f z _ (hh v))
  choose k p σ hk hp hσ hkB hpB hσB hkp hσσ hσp C hCc hC1 hCk using key
  have Jsq : ∀ v, Formalism.REAL.Jm (I.ε v) * Formalism.REAL.Jm (I.ε v) = 1 := by
    intro v
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hε : I.ε v a <;> simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, hε]
    · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.one_apply, hab]
  have hU : ∀ v (m : Matrix (Fin I.n) (Fin I.n) ℂ), Formalism.REAL.inUJ (I.ε v) m →
      ∃ u : Formalism.REAL.UJ (I.ε v), (((u : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m := by
    intro v m hm
    have hl : (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) * m = 1 := by
      have : Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v) * m =
          Formalism.REAL.Jm (I.ε v) * (mᴴ * Formalism.REAL.Jm (I.ε v) * m) := by
        simp only [Matrix.mul_assoc]
      rw [this, show mᴴ * Formalism.REAL.Jm (I.ε v) * m = Formalism.REAL.Jm (I.ε v) from hm, Jsq v]
    have hr : m * (Formalism.REAL.Jm (I.ε v) * mᴴ * Formalism.REAL.Jm (I.ε v)) = 1 := by
      first
      | exact mul_eq_one_comm.1 hl
      | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hl
    exact ⟨⟨⟨m, _, hr, hl⟩, hm⟩, rfl⟩
  choose ku hku using fun v => hU v (k v) (hk v)
  choose pu hpu using fun v => hU v (p v) (hp v)
  choose su hsu using fun v => hU v (σ v) (hσ v)
  let K : I.Ginf := fun v => ku v
  let P : I.Ginf := fun v => pu v
  let S : I.Ginf := fun v => su v
  have memH : ∀ (X : I.Ginf) (m : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ),
      (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) = m v) →
      (∀ v, m v * instBmat I v e f z = instBmat I v e f z) → X ∈ Hset I (frameSet I e f z) := by
    intro X m hX hmB v x hx
    show (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) *ᵥ _ = _
    rw [hX v]
    exact inst_fix_of v e f z (m v) (hmB v) x hx
  have ext' : ∀ X Y : I.Ginf, (∀ v, (((X v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (((Y v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) → X = Y := by
    intro X Y hXY
    funext v
    exact Subtype.ext (Units.ext (hXY v))
  have hSS : S * S = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, hsu]
    exact hσσ v
  have hSPSP : S * P * S * P = 1 := ext' _ _ fun v => by
    simp only [Pi.mul_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one, S, P, hsu, hpu]
    exact hσp v
  refine ⟨K, memH K k hku hkB, P, memH P p hpu hpB, S, memH S σ hsu hσB, ?_, ?_, ?_⟩
  · refine ext' _ _ fun v => ?_
    simp only [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, K, P, hku, hpu]
    exact hkp v
  · have hSi : S⁻¹ = S := inv_eq_of_mul_eq_one_right hSS
    rw [hSi]
    exact eq_inv_of_mul_eq_one_left hSPSP
  · refine ⟨Set.pi Set.univ C, isCompact_univ_pi hCc, ?_, ?_⟩
    · rw [interior_pi_set Set.finite_univ]
      intro v _
      exact hC1 v
    · intro x
      simp only [Set.mem_univ_pi]
      refine forall_congr' fun v => hCk v _ _ ?_
      have hg : (K * x * K⁻¹) v * ku v = ku v * x v := by
        simp [K]
      have := congrArg (fun g : Formalism.REAL.UJ (I.ε v) =>
        (((g : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) : Matrix (Fin I.n) (Fin I.n) ℂ)) hg
      simp only [Subgroup.coe_mul, Units.val_mul, hku] at this
      exact this

end PI.ScMuExists.UnitaryGroupMassFormula
