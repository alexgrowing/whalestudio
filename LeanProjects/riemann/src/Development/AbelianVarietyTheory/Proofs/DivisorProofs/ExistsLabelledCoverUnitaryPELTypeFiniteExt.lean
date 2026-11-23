import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordUniformisationUnitaryTypeTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionLabelsFiniteExtensionGaloisEquivariStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedCoverFiniteExtOfSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrimeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_odd_prime_isUnit_in_localRing (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ IsUnit (n : R) := by
  have h : IsUnit ((2 : R) * (3 : ℕ) + (-1) * (5 : ℕ)) := by
    have : (2 : R) * (3 : ℕ) + (-1) * (5 : ℕ) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, by decide, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by decide, isUnit_of_mul_isUnit_right h⟩

theorem exists_labCover_of_pelOK : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D' : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D'.toPre) ∧ Nonempty (LabCover D') := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hX hP
  have := hR.1.1
  have := hR.2
  obtain ⟨n, hn, ho, hu⟩ := exists_odd_prime_isUnit_in_localRing R
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := GlobalTheory.PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom φ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ (maximalIdeal V).comap φ := by rw [hc]; exact hna
    exact h1 ha⟩
  obtain ⟨DV, ⟨hDV⟩⟩ := GlobalTheory.MumPull.exists_pull R V φ hφ hloc D
  obtain ⟨_, oV, hPV⟩ := GlobalTheory.Mum.pelOK_of_isPullDeg R hR E H Dm D o hP V φ hφ DV ⟨hDV⟩
  have hXV : Nontrivial DV.toPre.X := hDV.xe.toEquiv.nontrivial
  obtain ⟨V', _, _, _, io, D', G', _, _, A', hV', hio, hfin, hD', hG', hU', hS'⟩ := GlobalTheory.T.exists_mumfordUniformisation_unitaryTypeTrait V hV E H Dm DV oV hXV hPV
  have hioloc : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  obtain ⟨R₁, _, _, _, ρ₁, D₁, A, lab, hf₁, hD₁, hS, h1, h2⟩ := GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension R hR D n hn ho hu V' hV' (io.comp φ)
    (hio.comp hφ) inferInstance D' G' A'
    (GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R V V' φ io _ _ _ hio ⟨hDV⟩ hD') hG' hU' hS'
  have hR₁ : Base R₁ := ⟨hf₁.1, charZero_of_injective_ringHom hf₁.2.1⟩
  have := hR₁.2
  obtain ⟨R₂, _, _, _, ρ₂, C, a, hf₂, hfib⟩ := GlobalTheory.T.exists_uniformised_cover_finite_ext_of_symmetric R₁ hR₁ A hS
  have hR₂ : Base R₂ := ⟨hf₂.1, charZero_of_injective_ringHom hf₂.2.1⟩
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ ρ₂ hf₂.2.1 (hf₂.2.2.to_isIntegral.isLocalHom hf₂.2.1) D₁
  obtain ⟨lab₂, k1, k2⟩ := GlobalTheory.T.exists_torsionLabels_finiteExtension_galoisEquivariant R₁ hR₁ D₁ A lab n h1 h2 R₂ ρ₂ hf₂ D₂ hD₂ C.A a hfib hn.pos
  have hu₂ : IsUnit (n : R₂) := by simpa using hu.map (ρ₂.comp ρ₁)
  exact ⟨R₂, _, _, _, ρ₂.comp ρ₁, D₂, ⟨hf₂.1, hf₂.2.1.comp hf₁.2.1, hf₂.2.2.comp hf₁.2.2⟩,
    GlobalTheory.Mum.nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ₁ ρ₂ _ _ _ hf₂.2.1 hD₁ hD₂,
    GlobalTheory.T.nonempty_labelled_cover_of_odd_prime R₂ hR₂ D₂ C lab₂ n hn ho hu₂ k1 k2⟩

end GlobalTheory.Mum
