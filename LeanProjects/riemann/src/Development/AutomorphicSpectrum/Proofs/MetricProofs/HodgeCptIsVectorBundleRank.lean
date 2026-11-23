import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.FlagBun

section Map

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem isFrameAt_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {b : Fin r → E} {p : Cpt ξ} (h : L.IsFrameAt b p) : (L.map f).IsFrameAt (fun a => f (b a)) p := by
  refine ⟨h.1.map' f (LinearMap.ker_eq_bot.2 hf), ?_⟩
  show (L p).map (f.restrictScalars (regAt ξ p)) = _
  rw [h.2, Submodule.map_span, ← Set.range_comp]
  rfl

theorem isVB_map_of_injective {L : Lat ξ E} {f : E →ₗ[Ω] E'} (hf : Function.Injective f) {r : ℕ}
    {V : Submodule Ω E} (h : L.IsVB r V) : (L.map f).IsVB r (V.map f) := by
  intro p hp
  obtain ⟨U, hU, b, hb, hq⟩ := h p hp
  refine ⟨U, hU, fun a => f (b a), ?_, fun q hqT hqU => isFrameAt_map_of_injective hf (hq q hqT hqU)⟩
  rw [← hb, Submodule.map_span, ← Set.range_comp]
  rfl

end Map

section Bundles

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω}

theorem inW_injective (A : HodgeCpt Y S x) : Function.Injective (inW A) :=
  LinearMap.inl_injective

theorem inO_injective (A : HodgeCpt Y S x) (τ : CMType H) : Function.Injective (inO A τ) := by
  intro a b h
  have e := congrFun (congrArg Prod.snd h) τ
  simpa [inO] using e

end Bundles

theorem LL_isVB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω]
    [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω)
    (𝔐 : HodgeCpt Y S x₀), ∀ s, (LL 𝔐 s).IsVB (rk (CMType H) D.p D.q s) (VV 𝔐 s) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 s
  rcases s with τ | τ
  · exact isVB_map_of_injective (inW_injective 𝔐) (𝔐.vb (.inl τ))
  · exact isVB_map_of_injective (inO_injective 𝔐 τ) (omBundle_isVB 𝔐 τ)

end GlobalTheory.CompanionTheory.Ar.PB.FMX
