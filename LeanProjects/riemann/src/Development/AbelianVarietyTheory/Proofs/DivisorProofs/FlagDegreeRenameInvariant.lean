import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.FlagPerm

theorem permExp_comp_perm {ι : Type} [Fintype ι] {N : ℕ} (σ : Equiv.Perm ι)
    (p : ι → Equiv.Perm (Fin N)) :
    permExp p = Finsupp.mapDomain (Prod.map σ id) (permExp (fun τ => p (σ τ))) := by
  have hinj : Function.Injective (Prod.map σ (id : Fin N → Fin N)) :=
    σ.injective.prodMap Function.injective_id
  ext ⟨a, i⟩
  obtain ⟨b, rfl⟩ := σ.surjective a
  have h := Finsupp.mapDomain_apply hinj (permExp (fun τ => p (σ τ))) (b, i)
  rw [show Prod.map σ (id : Fin N → Fin N) (b, i) = (σ b, i) from rfl] at h
  rw [h]
  rfl

theorem degFl_rename_perm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (σ : Equiv.Perm ι)
    (F : Pol ι N), degFl ι N (rename (Prod.map σ id) F) = degFl ι N F := by
  intro ι _ _ N σ F
  have hinj : Function.Injective (Prod.map σ (id : Fin N → Fin N)) :=
    σ.injective.prodMap Function.injective_id
  unfold degFl
  congr 1
  refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _ ?_
  intro p
  have e : (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N)))) p = fun τ => p (σ τ) := by
    funext τ
    simp
  rw [e, permExp_comp_perm σ p, coeff_rename_mapDomain _ hinj]
  congr 1
  exact (Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (p τ) : ℤ) : ℝ))).symm

end GlobalTheory.FlagPerm
