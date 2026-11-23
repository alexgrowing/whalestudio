import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relDim_le_of_formallyUnramified (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C] [Nontrivial C]
    [Algebra.FormallyUnramified B C] (g g' : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension g R B]
    [Algebra.IsStandardSmoothOfRelativeDimension g' R C] : g' ≤ g := by
  have : Nontrivial B := (algebraMap B C).domain_nontrivial
  have : Algebra.IsStandardSmooth R B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Module.Free B Ω[B⁄R] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange R B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map R B C x).mp (Subsingleton.elim _ _)
  have h1 := LinearMap.rank_le_of_surjective _ hs
  rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g', Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g] at h1
  simpa using h1

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_surjective_away {R B A L : Type} [CommRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra A L] (t : A) [IsLocalization.Away t L] [Nontrivial L] (φ : R →+* B) (ψ : B →+* A)
    (hψ : Function.Surjective ψ) (g g' : ℕ) (hφ : RingHom.IsStandardSmoothOfRelativeDimension g φ)
    (hL : RingHom.IsStandardSmoothOfRelativeDimension g' ((algebraMap A L).comp (ψ.comp φ))) :
    g' ≤ g := by
  letI : Algebra R B := φ.toAlgebra
  letI : Algebra B A := ψ.toAlgebra
  letI : Algebra B L := ((algebraMap A L).comp ψ).toAlgebra
  letI : Algebra R L := ((algebraMap A L).comp (ψ.comp φ)).toAlgebra
  haveI : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B A L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FormallyUnramified B A := Algebra.FormallyUnramified.of_surjective (Algebra.ofId B A) hψ
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyUnramified B L := Algebra.FormallyUnramified.comp B A L
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g R B := hφ
  haveI : Algebra.IsStandardSmoothOfRelativeDimension g' R L := hL
  exact relDim_le_of_formallyUnramified R B L g g'

end GlobalTheory

namespace GlobalTheory

theorem relDim_le_of_isClosedImmersion : ∀ (k : Type) [Field k] (N G : Over (Sp k)) (ν : N ⟶ G),
    IsClosedImmersion ν.left → Nonempty N.left → ∀ g g' : ℕ, SmoothOfRelativeDimension g G.hom →
    SmoothOfRelativeDimension g' N.hom → g' ≤ g := by
  intro k _ N G ν hν ⟨x⟩ g g' hG hN
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hG.exists_isStandardSmoothOfRelativeDimension (ν.left x)
  let V' : N.left.Opens := ν.left ⁻¹ᵁ V
  have hV' : IsAffineOpen V' := hV.preimage ν.left
  have hN' : SmoothOfRelativeDimension g' (ν.left ≫ G.hom) := by rw [Over.w ν]; exact hN
  have e' : V' ≤ (ν.left ≫ G.hom) ⁻¹ᵁ U := fun y hy => e hy
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g') _ hN' ⟨U, hU⟩ ⟨V', hV'⟩ e'
  have : Nonempty V' := ⟨⟨x, hx⟩⟩
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(N.left, V')
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1
      (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  have hψ : Function.Surjective (ν.left.appLE V V' le_rfl).hom := by
    have := ν.left.app_surjective V hV
    rw [Scheme.Hom.app_eq_appLE] at this
    exact this
  refine relDim_le_of_surjective_away (L := Localization.Away t) t (G.hom.appLE U V e).hom
    (ν.left.appLE V V' le_rfl).hom hψ g g' h ?_
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE ν.left G.hom U V V' e le_rfl]
  exact h₁

end GlobalTheory
