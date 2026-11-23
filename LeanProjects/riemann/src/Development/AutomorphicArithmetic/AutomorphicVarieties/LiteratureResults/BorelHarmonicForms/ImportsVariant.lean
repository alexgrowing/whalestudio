import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IndepAbs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indep :
    UpperTheory.V.Lit.Bor.Indep := by
  intro E _ _ _ a d q s π hπ ω h0 hV c hc
  have hind : iSupIndep fun i => (π i).V :=
    UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx)
      (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))
  have key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0 := by
    intro X k i
    have h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))),
        (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X := fun t f => by
      induction t using Finset.cons_induction with
      | empty => rfl
      | cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, AlternatingMap.add_apply, ih]
    have h1 : ∑ j, c j • cmp k (ω j X) = 0 := by
      have h2 := congrArg (fun η => cmp k (η X)) hc
      simpa only [h, map_sum, AlternatingMap.smul_apply, map_smul, AlternatingMap.zero_apply, map_zero] using h2
    exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X))
      (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)
  funext i
  by_contra hci
  refine h0 i (AlternatingMap.ext fun X => ?_)
  rw [← sum_cmp (ω i X), AlternatingMap.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]
