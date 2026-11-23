import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.totCont_of :
    GlobalTheory.GalV.VFin → DegCont → TotCont := by
  classical
  intro hVF hDC l _ k Ω _ _ _ _ hl X p hp v μ
  haveI := hp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hu : IsUnit (l : Ω) := by
    have h := (map_ne_zero (algebraMap k Ω)).mpr hl
    rw [map_natCast] at h
    exact h.isUnit
  have hfin : ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n 0) := fun n =>
    (hVF l Ω hu (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) n 0).1
  have hv : ∀ σ, μ (galTot l Ω p σ v) = ∑ n ∈ v.support,
      (μ ∘ₗ DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj (geom Ω p)) n 0) n)
        (galHQ l Ω p n 0 σ (v n)) := by
    intro σ
    conv_lhs => rw [← DirectSum.sum_support_of v]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.comp_apply]
    congr 1
    exact DirectSum.lmap_lof (fun n => galHQ l Ω p n 0 σ) n (v n)
  simp_rw [hv]
  exact continuous_finset_sum _ fun n _ => hDC l k Ω p inferInstance inferInstance n 0 (hfin n) (v n) _
