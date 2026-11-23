import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipDef :
    UpperTheory.V.Lit.Bor.IpDef := by
  intro E _ _ _ a n e he M _ _ _ _ H N hH q
  refine ⟨fun ω η => ?_, fun ω hω => ⟨?_, fun h0 => ?_⟩⟩
  · simp only [ip, map_sum]
    exact Finset.sum_congr rfl fun I _ => hH.herm _ _
  · simp only [ip, Complex.re_sum]
    exact Finset.sum_nonneg fun I _ => hH.nonneg _ (hω _)
  · have hre : ∑ I : Fin q → Fin n, (H (ω fun i => e (I i)) (ω fun i => e (I i))).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re h0
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hH.nonneg _ (hω _))).1 hre
    have h2 : ∀ I : Fin q → Fin n, (ω fun i => e (I i)) = 0 := fun I => by
      refine hH.definite _ (hω _) (Complex.ext (h1 I (Finset.mem_univ _)) ?_)
      exact Complex.conj_eq_iff_im.1 (hH.herm _ _).symm
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : ω X = ∑ I : Fin q → Fin n, ω fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact ω.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [ω.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
