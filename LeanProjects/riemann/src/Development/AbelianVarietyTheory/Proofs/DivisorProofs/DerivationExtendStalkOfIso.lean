import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendLocalizationAtPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDer

theorem derivation_extend_stalk_of_iso : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  intro X X' f _ U d x hx
  have hU' : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let φ : Γ(X, U.1) ≃+* Γ(X', f ⁻¹ᵁ U.1) := (asIso (f.app U.1)).commRingCatIsoToRingEquiv
  letI : Algebra Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) :=
    X'.presheaf.algebra_section_stalk (⟨x, hx⟩ : f ⁻¹ᵁ U.1)
  haveI := hU'.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ a, algebraMap Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x) a =
      (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom a := fun a => rfl
  let g : Γ(X', f ⁻¹ᵁ U.1) →+ X'.presheaf.stalk x :=
    (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom.toAddMonoidHom.comp
      (φ.toRingHom.toAddMonoidHom.comp (d.toLinearMap.toAddMonoidHom.comp φ.symm.toRingHom.toAddMonoidHom))
  have hg : ∀ a, g a = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom (φ (d (φ.symm a))) := fun a => rfl
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ Γ(X', f ⁻¹ᵁ U.1) (X'.presheaf.stalk x)
    (hU'.primeIdealOf ⟨x, hx⟩).asIdeal
    (intDerivationOfLeibniz g (fun a b => by
      simp only [hg, map_mul, Derivation.leibniz, smul_eq_mul, map_add, Algebra.smul_def, halg,
        RingEquiv.apply_symm_apply]))
  refine ⟨D', fun r => ?_⟩
  have h1 := hD' (φ r)
  rw [halg] at h1
  refine h1.trans ?_
  show g (φ r) = _
  rw [hg, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.StalkDer
