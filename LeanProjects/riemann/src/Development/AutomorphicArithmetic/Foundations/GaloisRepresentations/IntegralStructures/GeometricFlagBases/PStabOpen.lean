import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.stabOpen_of :
    HtDesc → StabOpen := by
  intro h l _ k Ω _ _ _ _ X p hqc hqs n i x m
  obtain ⟨L, hL, z, hz⟩ := h (l ^ m) k Ω p hqc hqs n i (x.1 m)
  have fix : ∀ τ ∈ L.fixingSubgroup,
      GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m := by
    intro τ hτ
    rw [← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g * σ⁻¹ ∈ L.fixingSubgroup := hg
    have e : g = (g * σ⁻¹) * σ := by group
    show ((galHl l Ω p n i g) x).1 m = x.1 m
    rw [e, map_mul, Module.End.mul_apply]
    change GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n
      (((galHl l Ω p n i σ) x).1 m) = x.1 m
    have hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m := hσ
    rw [hσ']
    exact fix _ hg'
  · exact (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_right σ⁻¹)
  · show σ * σ⁻¹ ∈ L.fixingSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
