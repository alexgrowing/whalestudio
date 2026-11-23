import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasString
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.multiset_map_prod_finset_sum {α β γ : Type} [CommMonoid γ] (F : α → γ) (s : Finset β)
    (m : β → Multiset α) :
    ((∑ i ∈ s, m i).map F).prod = ∏ i ∈ s, ((m i).map F).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Multiset.map_add, Multiset.prod_add, ih]

theorem GlobalTheory.satake_linear_factors_regroup : ∀ (K : Type) [Field K] (ι : K ≃+* ℂ) (c : ℕ) (d : Fin c → ℕ) (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (q : ℕ),
  q ≠ 0 → ∀ e : ℂ,
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) = T.map (fun z => (z : ℂ)) →
  (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))).prod =
    ∏ i, ∏ k : Fin (d i), ((S i).map fun z : ℂˣ =>
      Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ (e + (((d i : ℂ) - 1) / 2 - (k : ℕ)))))).prod := by
  intro K _ ι c d S T q hq e hT
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  set F : ℂ → Polynomial K := fun u => Polynomial.X - Polynomial.C (ι.symm (u * (q : ℂ) ^ e)) with hF
  have h1 : (T.map fun z : ℂˣ => Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * (q : ℂ) ^ e))) =
      (T.map (fun z : ℂˣ => (z : ℂ))).map F := by
    rw [Multiset.map_map]; rfl
  have hc : ∀ M : Multiset ℂˣ, (do let a ← M; pure (a : ℂ) : Multiset ℂ) = M.map (fun z : ℂˣ => (z : ℂ)) :=
    fun M => Multiset.bind_singleton M _
  simp only [hc, Multiset.map_id'] at hT
  rw [h1, ← hT, GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [GlobalTheory.multiset_map_prod_finset_sum]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl (fun z _ => ?_)
  simp only [Function.comp, hF]
  rw [Complex.cpow_add _ _ hq']
  ring_nf
