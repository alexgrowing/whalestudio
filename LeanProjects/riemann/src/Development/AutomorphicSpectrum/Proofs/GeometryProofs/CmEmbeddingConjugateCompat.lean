import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab

theorem exists_labelEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (t : CMType H ⊕ CMType H), ∃ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) ∧ (∀ a : 𝓞 E, (σ.comp (HT.cmConj E).toRingHom) (a : E) = 𝔐.emb t.swap a) ∧ ∀ σ' : E →+* Ω, (∀ a : 𝓞 E, σ' (a : E) = 𝔐.emb t a) → σ' = σ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 t
  have uniq : ∀ f g : E →+* Ω, (∀ a : 𝓞 E, f (a : E) = g (a : E)) → f = g := by
    intro f g h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext a
    exact h a
  rcases t with τ | τ
  · let σ : E →+* Ω := 𝔐.cst.comp (τ.1.codRestrict c.F (c.conj τ.1))
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inl τ) a := fun a => rfl
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
    rw [H.bar_eq a]
  · let σ : E →+* Ω :=
      𝔐.cst.comp ((τ.1.codRestrict c.F (c.conj τ.1)).comp (GlobalTheory.CompanionTheory.Ar.HT.cmConj E).toRingHom)
    have h1 : ∀ a : 𝓞 E, σ (a : E) = 𝔐.emb (Sum.inr τ) a := by
      intro a
      change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (NumberField.IsCMField.complexConj E (a : E))) =
        𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) ((H.bar a : 𝓞 E) : E))
      rw [H.bar_eq a]
    refine ⟨σ, h1, ?_, fun σ' h => uniq _ _ (fun a => (h a).trans (h1 a).symm)⟩
    intro a
    change 𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1)
        (NumberField.IsCMField.complexConj E (NumberField.IsCMField.complexConj E (a : E)))) =
      𝔐.cst (τ.1.codRestrict c.F (c.conj τ.1) (a : E))
    rw [NumberField.IsCMField.complexConj_apply_apply]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Lab
