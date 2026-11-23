import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem basis_image {Ω M N ι : Type} [Field Ω] [AddCommGroup M] [Module Ω M] [AddCommGroup N] [Module Ω N]
    (b : Module.Basis ι Ω M) (f : M →ₗ[Ω] N) (hf : Function.Injective f) :
    LinearIndependent Ω (fun a => f (b a)) ∧
      Submodule.span Ω (Set.range fun a => f (b a)) = (⊤ : Submodule Ω M).map f := by
  refine ⟨b.linearIndependent.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  have h : (Set.range fun a => f (b a)) = f '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, Submodule.span_image, b.span_eq]

theorem inW_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x) :
    Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (A : HodgeCpt Y S x)
    (τ : CMType H) : Function.Injective (inO A τ) := by
  classical
  unfold inO
  rw [LinearMap.coe_comp]
  refine LinearMap.inr_injective.comp ?_
  rw [LinearMap.coe_single]
  exact Pi.single_injective τ

theorem cc_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO s
  rcases s with τ | τ
  · have h := basis_image (bW τ) ((inW 𝔐).comp (𝔐.Vgen (.inl τ)).subtype)
      ((inW_injective 𝔐).comp Subtype.val_injective)
    rw [Submodule.map_comp, Submodule.map_subtype_top] at h
    exact h
  · exact basis_image (bO τ) (inO 𝔐 τ) (inO_injective 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases
