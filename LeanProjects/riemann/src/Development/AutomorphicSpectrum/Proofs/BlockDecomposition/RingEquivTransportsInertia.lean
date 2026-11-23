import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.InvTransport

theorem exists_invFam : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ hDec l _ r hcyc inv
  have hcm : ∀ (A' : ValuationSubring Ω') (x : Ω), E x ∈ A' ↔ x ∈ A'.comap E.toRingHom :=
    fun A' x => Iff.rfl
  let eD : ∀ A' : ValuationSubring Ω',
      Dec (F := F) (A'.comap E.toRingHom) ≃ₜ* Dec (F := F') A' :=
    fun A' => subgroupIso Φ _ _ (hDec _ A' (hcm A'))
  have hc : ∀ (A' : ValuationSubring Ω') (h : Dec (F := F) (A'.comap E.toRingHom))
      (m : ZMod (l ^ r)),
      (muLoc F' l r A') (eD A' h) m = (muLoc F l r (A'.comap E.toRingHom)) h m := by
    intro A' h m
    have h1 : cycMod F' Ω' l r (Φ h.1) = cycMod F Ω l r h.1 := hcyc h.1
    show charRep ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) m =
      charRep ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h m
    have h2 : ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) =
        ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h := h1
    rw [charRep_apply, charRep_apply, h2]
  refine ⟨fun A' => inv (A'.comap E.toRingHom) ∘ₗ
    (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A')).toLinearMap, ?_⟩
  intro A A' hA
  obtain rfl : A = A'.comap E.toRingHom := by
    ext x
    exact (hA x).symm.trans (hcm A' x)
  refine ⟨fun hb => hb.comp (LinearEquiv.bijective _), fun z z' hz => ?_⟩
  show inv (A'.comap E.toRingHom) (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A') (Submodule.Quotient.mk z')) = _
  rw [ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk]
  congr 2
  apply Subtype.ext
  funext p
  exact hz p.1 p.2 (eD A' p.1) (eD A' p.2) rfl rfl

end GlobalTheory.CompanionTheory.PTIso.InvTransport
