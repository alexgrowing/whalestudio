import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompactStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

open GlobalTheory.UnimodMass in
theorem GlobalTheory.UnimodMass.umax_relIndex_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) ≠ 0 ∧ ((Umax L n).map (MulAut.conj h).toMonoidHom).relIndex (Umax L n) = (Umax L n).relIndex ((Umax L n).map (MulAut.conj h).toMonoidHom) := by
  intro L _ _ _ n h
  set U := Umax L n with hUdef
  set V := U.map (MulAut.conj h).toMonoidHom with hVdef
  haveI hW : Finite (DC (GQ L n) (U ⊓ V)) := finite_dc_of_cover (GlobalTheory.T.exists_finset_doubleCosets_conj_maxCompact L n h)
  have hb : IsBounded U := ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using hκ⟩⟩
  have hU : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ U} := fun t => GlobalTheory.T.finite_rational_conj_mem_boundedCompact L n U hb t
  have hV : ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} := by
    intro t
    haveI := hU (t * h)
    refine Finite.of_injective (fun x : {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ V} =>
      (⟨x.1, ?_⟩ : {γ : GQ L n // (t * h)⁻¹ * (γ : GAf L n) * (t * h) ∈ U})) ?_
    · have hx : t⁻¹ * ((x.1 : GQ L n) : GAf L n) * t ∈ U.map (MulAut.conj h).toMonoidHom := x.2
      rw [Subgroup.mem_map_equiv] at hx
      simpa [MulAut.conj_symm_apply, mul_assoc] using hx
    · intro a b hab
      exact Subtype.ext (by simpa using congrArg Subtype.val hab)
  obtain ⟨h1, e1⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) U inf_le_left hW hU
  obtain ⟨h2, e2⟩ := GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass (GAf L n) (GQ L n) (U ⊓ V) V inf_le_right hW hV
  have e3 : mass (GQ L n) V = mass (GQ L n) U := mass_conj (GQ L n) U h
  haveI : Finite (DC (GQ L n) U) := finite_dc_of_le (Γ := GQ L n) (W := U ⊓ V) inf_le_left
  have hpos := mass_pos (Γ := GQ L n) (K := U) hU
  rw [Subgroup.inf_relIndex_left] at h1 e1
  rw [Subgroup.inf_relIndex_right] at h2 e2
  refine ⟨h1, ?_⟩
  rw [e3] at e2
  have : (V.relIndex U : ℚ) = (U.relIndex V : ℚ) := mul_right_cancel₀ hpos.ne' (e1.symm.trans e2)
  exact_mod_cast this
