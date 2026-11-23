import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem dg_mulVec {Γ k : Type} [Group Γ] [Field k] {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ)
    (u : Fin t → k) (i : Fin t) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec u i = (a i g : k) * u i := by
  simp [dg, Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.TP.Sub.eigSum_holds :
    EigSum := by
  intro Γ k _ _ m t r a c
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    let e : Fin t → k := Pi.single i 1
    let w : Fin (m + t) → k := fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e
    have hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0 := by
      funext y
      simp [w]
    have hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e := by
      funext y
      simp [w]
    refine ⟨w, ?_, ?_⟩
    · intro h
      have := congrFun hwr i
      rw [h] at this
      simp [e] at this
    · intro g
      funext x
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
      rcases y with y | y
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]
        have := congrFun hwl y
        simp only [Function.comp_apply] at this
        rw [this]
        simp
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]
        have := congrFun hwr y
        simp only [Function.comp_apply] at this
        rw [Pi.smul_apply, this, smul_eq_mul]
        by_cases hy : y = i
        · subst hy
          rw [hi]
        · simp [e, Pi.single_apply, hy]
  · intro hne hex
    obtain ⟨w, hw0, hw⟩ := hex
    rcases GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext hcon)
      apply hne j
      ext g
      have := congrFun (hv g) j
      rw [dg_mulVec, Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
