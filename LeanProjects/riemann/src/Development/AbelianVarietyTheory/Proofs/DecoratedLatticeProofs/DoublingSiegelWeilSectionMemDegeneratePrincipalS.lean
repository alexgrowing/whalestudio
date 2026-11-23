import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLawStatement

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause lagr evZero)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.SwSecMem

variable {D : D7} (A B : HSp D) (omh : WRep (dblSp A) B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def intSub : Submodule ℂ (WO (dblSp A) B → ℂ) where
  carrier := {f | ∀ g : GA D (dblSp A), IntegrableOn (fun w => omh (g, 1) f (lagr A B w)) 𝓕 ν}
  zero_mem' g := by
    simp only [map_zero, Pi.zero_apply]
    exact integrableOn_zero
  add_mem' {f f'} hf hf' g := by
    simp only [map_add, Pi.add_apply]
    exact Integrable.add (hf g) (hf' g)
  smul_mem' c f hf g := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact Integrable.const_mul (hf g) c

def swLin : intSub A B omh ν 𝓕 →ₗ[ℂ] (GA D (dblSp A) → ℂ) where
  toFun f := swSec A B omh ν 𝓕 f
  map_add' f f' := by
    funext g
    simp only [swSec, evZero, Submodule.coe_add, map_add, Pi.add_apply]
    exact integral_add (f.2 g) (f'.2 g)
  map_smul' c f := by
    funext g
    simp only [swSec, evZero, Submodule.coe_smul, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem swSec_mul (φ : WO (dblSp A) B → ℂ) (g k : GA D (dblSp A)) :
    swSec A B omh ν 𝓕 φ (g * k) = swSec A B omh ν 𝓕 (omh (k, 1) φ) g := by
  have : ((g * k, 1) : GA D (dblSp A) × GA D B) = (g, 1) * (k, 1) := by simp
  simp only [swSec]
  rw [this, map_mul, Module.End.mul_apply]

theorem swSec_mem_degPS : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  intro hW D ψ A B χB omh hω ν 𝓕 hν φ hφ a hK
  have hint : ∀ f, IsThetaFunO ψ (dblSp A) B f → f ∈ intSub A B omh ν 𝓕 := fun f hf g =>
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν _ (hω.om_pres (g, 1) f hf)).1
  refine (mem_degPS A a).2 ⟨GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh hω ν 𝓕 hν φ hφ,
    (GlobalTheory.T.siegelWeilSection_integrable_and_continuous D ψ A B χB omh hω ν 𝓕 hν φ hφ).2, ?_⟩
  let S := Submodule.span ℂ {f : WO (dblSp A) B → ℂ | ∃ k ∈ Khat A a, f = omh (k, 1) φ}
  haveI : FiniteDimensional ℂ S := hK
  have hS : S ≤ intSub A B omh ν 𝓕 := Submodule.span_le.2 (by
    rintro _ ⟨k, -, rfl⟩
    exact hint _ (hω.om_pres _ _ hφ))
  refine isKFinite_iff.2 ⟨LinearMap.range ((swLin A B omh ν 𝓕).comp (Submodule.inclusion hS)), inferInstance,
    fun k hk => ⟨⟨omh (k, 1) φ, Submodule.subset_span ⟨k, hk, rfl⟩⟩, funext fun g => ?_⟩⟩
  exact (swSec_mul A B omh ν 𝓕 φ g k).symm

end GlobalTheory.SwSecMem

end
