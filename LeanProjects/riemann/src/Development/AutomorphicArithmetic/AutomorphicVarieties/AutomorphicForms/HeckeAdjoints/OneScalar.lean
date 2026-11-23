import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.HasPairingOfHerm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
open NumberField IsDedekindDomain Matrix Formalism.L2.Host UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Gk

theorem UpperTheory.V.Af.Gk.oneScalar :
    UpperTheory.V.Af.Gk.OneScalar := by
  intro F _ _ _ a π
  classical
  refine TR.Cen.exists_scalar π ?_
  have ht : ∀ v : InfinitePlace F, ∑ i, TR.Eop (a := a) v i i ∈ TR.Zalg F a := fun v =>
    GlobalTheory.CuspRep.Central.trace_mem (TR.Eop (a := a) v) (Subalgebra.toSubmodule (TR.Zalg F a)) (one_mem (TR.Zalg F a))
      fun u => by
        have h : TR.cap (a := a) v (u - ((a : ℂ) - 1) / 2) ∈ TR.Zalg F a := Algebra.subset_adjoin ⟨v, _, rfl⟩
        have e : TR.cap (a := a) v (u - ((a : ℂ) - 1) / 2) =
          Formalism.REAL.qdet (TR.Eop (a := a) v) (u - ((a : ℂ) - 1) / 2 + ((a : ℂ) - 1) / 2) := rfl
        rw [e, sub_add_cancel] at h
        exact h
  have hX : TR.lie F a (oneL F a) = ∑ i, TR.lieS F a i i 1 := by
    simp only [TR.lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.sum_single_one (m := Fin a) (α := TR.Rinf F)).symm
  have h1 : ∀ i, TR.lieS F a i i 1 = ∑ v, TR.Eop (a := a) v i i := fun i => by
    rw [← Finset.univ_sum_single (1 : TR.Rinf F), map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [TR.Eop_eq]
    congr
  rw [hX, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  exact sum_mem fun v _ => ht v
