import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LevelCo
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PiHarm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CuspSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.InclFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.harmEx :
    UpperTheory.V.Lit.Bor.HarmEx := by
  intro E _ _ _ a ha n e he U hU π Ξ r hr hC hF
  obtain ⟨q, ω, h0, hK, hB, hL⟩ := levelCo E a U hU π Ξ hC hF
  obtain ⟨hd, hδ⟩ := piHarm E a ha n e he π Ξ r hr hC q ω hK
  obtain ⟨hinj, hcmp, hIK, hIL, hIA⟩ := inclFacts E a π Ξ r
  have hE := oneEig E a π Ξ r hr hC
  have hS := cuspSq E a ha π r hE
  refine ⟨q, inclCo π Ξ ω, fun h => h0 (AlternatingMap.ext fun X => hinj ?_),
    ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, AlternatingMap.ext fun X => ?_, ?_⟩,
    fun X => mem_tens.2 fun i => ?_⟩
  · have h1 : incl π Ξ (ω X) = 0 := DFunLike.congr_fun h X
    rw [h1, AlternatingMap.zero_apply, map_zero]
  · rw [inclCo_apply, inclCo_apply, hK k X, hIK]
  · rw [inclCo_apply, hB X i hi, map_zero]
  · rw [inclCo_apply, hcmp]
    have hm := (cmp i (ω X)).2
    refine ⟨⟨(hS _ hm).left, fun u hu => congrArg Subtype.val (hL X i u hu), fun m hm' => ?_⟩,
      (π.cusp _ hm).2, (hS _ hm).sq⟩
    have h1 : (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) = m • 1 := hr.symm.trans hm'
    have h2 : (r : ℂ) = m := by simpa using congrFun (congrFun h1 i) i
    rw [← h2]
    exact hE _ hm
  · have h1 := congrArg (incl π Ξ) (DFunLike.congr_fun hd X)
    rw [dCo_apply, AlternatingMap.zero_apply, map_zero, map_sum] at h1
    rw [dCo_apply, AlternatingMap.zero_apply, ← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inclCo_apply, ← hIL]
    simp only [map_zsmul, LinearMap.map_smul_of_tower]
  · cases q with
    | zero => trivial
    | succ q =>
      refine AlternatingMap.ext fun X => ?_
      have h1 := congrArg (incl π Ξ) (DFunLike.congr_fun (show del _ e ω = 0 from hδ) X)
      rw [del_apply, AlternatingMap.zero_apply, map_zero, map_sum] at h1
      rw [del_apply, AlternatingMap.zero_apply, ← h1]
      exact Finset.sum_congr rfl fun j _ => (hIA _ _).symm
  · rw [inclCo_apply, hcmp]
    exact (cmp i (ω X)).2
