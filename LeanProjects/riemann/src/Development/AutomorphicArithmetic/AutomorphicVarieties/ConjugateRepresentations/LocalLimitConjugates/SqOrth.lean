import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.sqOrth :
    UpperTheory.V.Cj.H.SqOrth := by
  intro E _ _ _ a ha n e he Ξ r q
  obtain ⟨G, hG⟩ := admEx E a Ξ
  obtain ⟨H, hH⟩ := petEx E a ha r
  have hv : ∀ {k : ℕ} {ω : Co Ξ k}, Val (sqSub E a r) ω → ∀ X, ω X ∈ tens Ξ.d (sqSub E a r) :=
    fun h X => mem_tens.2 (h X)
  have hadj := ipAdj E a n e _ (smLie Ξ) (smAdj Ξ r) (tform H G) _ (smForm E a Ξ r H G hH hG)
  have hdef := ipDef E a n e he _ (tform H G) _ (tformPos _ _ H _ G hH.pos hG.pos)
  refine ⟨?_, fun ω h1 h2 h3 => ?_⟩
  · cases q with
    | zero => exact fun ω _ _ h => h
    | succ q =>
      rintro ω h1 h2 ⟨η, hη, rfl⟩
      have h3 := hadj q _ η (hv h1) (hv hη)
      have h4 : del (smAdj Ξ r) e (dCo (smLie Ξ) η) = 0 := h2
      refine ((hdef (q + 1)).2 _ (hv h1)).2 ?_
      rw [h3, h4]
      simp [ip]
  · have h4 := hadj q ω _ (hv h1) (hv h2)
    rw [h3] at h4
    refine ((hdef q).2 _ (hv h2)).2 ?_
    have h5 : ip e (tform H G) ω 0 = 0 := by simp [ip]
    have h6 : ((q : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero q
    exact (mul_eq_zero.1 (h4.symm.trans h5)).resolve_left h6
