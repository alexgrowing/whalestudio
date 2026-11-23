import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.Xgn.exists_cm_type_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) →
      ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
    intro σ hσ σ' hσ'
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
      (RingHom.ext fun a => (hσ' a).trans (hσ a).symm)
  rcases t with τ | τ
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, φ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨φ, h1, fun a => ?_, uniq φ h1⟩
    show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq]
  · let φ : E →+* Ω := 𝔐.cst.comp ((τ : E →+* ℂ).codRestrict c.F (c.conj τ))
    have h1 : ∀ a : 𝓞 E, (φ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      show φ (IsCMField.complexConj E (a : E)) = φ ((H.bar a : 𝓞 E) : E)
      rw [H.bar_eq]
    refine ⟨φ.comp (HT.cmConj E).toRingHom, h1, fun a => ?_, uniq _ h1⟩
    show φ (IsCMField.complexConj E (IsCMField.complexConj E (a : E))) = φ (a : E)
    rw [IsCMField.complexConj_apply_apply]
