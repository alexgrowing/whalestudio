import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CompactConjugacyDomainLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptInputs

theorem order_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {F' : Type} [Field F']
    [NumberField F'] (ψ : F' →+* Ω) (L : Lat ξ Ω) (s : Ω) (v : HeightOneSpectrum (𝓞 F')) (π : F')
    (hπ : v.valuation F' π = WithZero.exp (-1 : ℤ)) (p : Cpt ξ)
    (hp : ∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) (hf : ¬ unitAt ξ p (ψ π)) {ρ ρ' : ℚ}
    (h : ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * ρ ∧ ∀ p : Cpt ξ,
      (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L s (ψ π) m k p)
    (h' : ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * ρ' ∧ ∀ p : Cpt ξ,
      (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L s (ψ π) m k p) : ρ = ρ' := by
  obtain ⟨m, k, hm, hk, hO⟩ := h
  obtain ⟨m', k', hm', hk', hO'⟩ := h'
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact absurd hπ.symm WithZero.exp_ne_zero
  have h0 : ψ π ≠ 0 := (map_ne_zero ψ).2 hπ0
  have hle : v.valuation F' π ≤ 1 := by
    rw [hπ]
    exact oneLePart_eq_one.mp rfl
  have hreg : ψ π ∈ regAt ξ p := hp π hle
  have hr := OrderAt.ratio_unique h0 hreg hf (hO p hp) (hO' p hp)
  have hq : (k : ℚ) * (m' : ℚ) = (k' : ℚ) * (m : ℚ) := by exact_mod_cast hr
  rw [hk, hk'] at hq
  have hm0 : (m : ℚ) * (m' : ℚ) ≠ 0 := mul_ne_zero (by exact_mod_cast hm.ne') (by exact_mod_cast hm'.ne')
  apply mul_left_cancel₀ hm0
  calc (m : ℚ) * m' * ρ = (m * ρ) * m' := by ring
    _ = (m' * ρ') * m := hq
    _ = m * m' * ρ' := by ring

theorem div_mem_lineLat {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ)
    {α β : Ω} (hα : α ≠ 0) (hβ : β ≠ 0) (hA : A.wedge p x = Submodule.span (regAt ξ x) {α • a})
    (hB : B.wedge q x = Submodule.span (regAt ξ x) {β • b}) : α / β ∈ lineLat A B p q a b x :=
  Submodule.subset_span ⟨β / α, ⟨α, β, hα, hβ, hA, hB, div_mul_cancel₀ _ hα⟩, (inv_div _ _).symm⟩

theorem const_case (hI : CptFlatInputs) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c))
    (Z : CptOver Y U) (φ : FrameFn Xo c) (τ : CMType H) (t : (c.F →+* ℂ) → ℝ) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (A : HermLine J) (n : ℕ) :
    Z.IsGeom → FlatOnModel Z τ.1 φ → (∀ s, HasInfNorm U τ.1 φ s (t s)) →
    genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) →
    (∀ x : Ω, (∃ f : Polynomial c.F, f ≠ 0 ∧ f.eval₂ 𝔐.cst x = 0) → x ∈ Set.range 𝔐.cst) →
    Birational y → IsArithVar (mCoordIdeal y) n →
    Fl.RootLines xdeg e → (∀ r, Fl.IsHodgeLine r (e r) (hx r)) →
    IsSmoothHerm A → IsConjInvariantH A → A.a = ∑ i, xdeg (τ, i) →
    (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
      A.h w = ∏ i, (hx (τ, i)).h w) →
    (∀ p ∈ S, ExactModLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (p : Ω) (D.p + D.q)) →
    (∀ p : ℕ, p.Prime → p ∉ S →
      NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ))
        (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (p : Ω)) →
    ∃ c₀ : Ω, c₀ ≠ 0 ∧ ∀ (σ : c.F →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y 𝔐.cst σ z → IsMultiHomog g dg →
        IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h →
          ‖evC z g‖ = Real.exp (t σ) * A.h z * ‖evC z h‖ := by
  intro hgeo hflat hnorm hgen halg hbir harith hroot hhodge hsm hconj ha hh hex hnum
  obtain ⟨c₀, r, cinf, hc₀, hcinf, -, -, -, hfin⟩ := hI E H D l Xo c Y U Z φ τ t S Ω K J y 𝔐 Fl xdeg e hx A n c.F
    (RingHom.id c.F) 𝔐.cst hgeo hflat hnorm hgen (RingHom.comp_id _) halg hbir harith hroot hhodge hsm hconj ha hh
    hex hnum
  refine ⟨c₀, hc₀, fun σ z g h dg dh hz hg hh' hd hgh => ?_⟩
  rw [hfin σ z g h dg dh hz hg hh' hd hgh, hcinf σ, RingHom.comp_id]

theorem labelEmb_inr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inr τ) = tauIn c (ComplexEmbedding.conjugate τ.1) := by
  ext a
  show τ.1 ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ.1 (a : E)
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj (K := E) τ.1 (a : E)

theorem labelEmb_inl {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : CMType H) : labelEmb c (.inl τ) = tauIn c τ.1 := rfl

end GlobalTheory.CompanionTheory.Ar.Flat.CptInputs
