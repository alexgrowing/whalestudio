import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CharpolyEqOfIsNilpotentSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormVZpowDegEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

theorem restricts_of_isFrobSS : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (X Y : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Weil h) X) (N : Module.End ℂ X) (a : WDRep h X) (ρ' : Representation ℂ (Weil h') Y) (N' : Module.End ℂ Y) (b : WDRep h' Y), IsSmooth ρ → IsSmooth ρ' → IsFrobSS ⇑ρ N a → IsFrobSS ⇑ρ' N' b → ∀ e : X ≃ₗ[ℂ] Y, (∀ (σ : Weil h) (σ' : Weil h'), (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) → ∀ x, e (ρ σ x) = ρ' σ' (e x)) → (∀ x, e (N x) = N' (e x)) → Restricts (WD.mk a) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' X Y _ _ _ _ _ _ ρ N a ρ' N' b _ _ ha hb e hρ hN
  let f := (Module.finBasis ℂ X).equivFun
  let a₁ := a.transport f
  let b₀ := ResEx.resRep h h' a₁
  let g : Y ≃ₗ[ℂ] (Fin (Module.finrank ℂ X) → ℂ) := e.symm.trans f
  let ρ'' : Weil h' → Module.End ℂ (Fin (Module.finrank ℂ X) → ℂ) :=
    fun σ' => f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ'))
  let N'' := f.conjAlgEquiv ℂ N
  have hss : IsFrobSS ρ'' N'' b₀ := by
    refine ⟨?_, fun σ' => ?_⟩
    · show f.conjAlgEquiv ℂ a.N = _
      rw [ha.1]
    · show Commute (f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ'))) _ ∧ IsNilpotent (_ - f.conjAlgEquiv ℂ (a.ρ (ResEx.resW h h' σ')))
      refine ⟨(ha.2 (ResEx.resW h h' σ')).1.map (f.conjAlgEquiv ℂ), ?_⟩
      have := (ha.2 (ResEx.resW h h' σ')).2.map (f.conjAlgEquiv ℂ)
      rwa [map_sub] at this
  have hiso : b.Iso b₀ := by
    refine IsFrobSS.iso hb hss g (fun σ' y => ?_) (fun y => ?_)
    · have h1 := hρ (ResEx.resW h h' σ') σ' (fun _ => rfl) (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (ρ' σ' y)) = f.conjAlgEquiv ℂ (ρ (ResEx.resW h h' σ')) (f (e.symm y))
      rw [← h1]
      simp
    · have h1 := hN (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h1
      show f (e.symm (N' y)) = f.conjAlgEquiv ℂ N (f (e.symm y))
      rw [← h1]
      simp
  refine ⟨_, a₁, b₀, WD.sound (a.iso_transport f).symm, (WD.sound hiso).symm, rfl, fun σ σ' hs => ?_⟩
  show a₁.ρ (ResEx.resW h h' σ') = a₁.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL
