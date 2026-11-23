import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIndexConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
