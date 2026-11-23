import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SabMapCancelAndCompOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTriplePullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

theorem locMod_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  intro E _ _ _ H Dw l Xo c _ z T iK
  refine ⟨fun h => ?_, fun M T' ψ i hψ => ?_⟩
  · have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
    let ρ : 𝓞 z.K →+* T.V := e.symm.toRingHom.comp
      ((iK.comp (algebraMap (𝓞 z.K) z.K)).codRestrict (algebraMap T.V T.Fr).range fun a => h a)
    have hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K) := by
      ext a
      exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h a⟩)
    obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ρ z.B).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ iK z.Φ.T).1
    obtain ⟨m1, h1⟩ := sab_comp_exists n' z.Φ.m _ rfl
    obtain ⟨k, hk⟩ := sab_comp_exists n' z.m' _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T.V T.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hρ])
    exact ⟨⟨ρ, hρ, G, t', n, n', m1, m2, h1, h2.trans hk⟩⟩
  · obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ψ M.G).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ i M.t').1
    obtain ⟨N, hN⟩ := sab_comp_exists n M.n _ (spectrumMap_comp M.ρ ψ)
    obtain ⟨N', hN'⟩ := sab_comp_exists n' M.n' _ (spectrumMap_comp iK i)
    obtain ⟨m1, h1⟩ := sab_comp_exists n' M.m1 (spMap (i.comp iK) ≫ z.x)
      (by rw [spectrumMap_comp, Category.assoc])
    obtain ⟨k, hk⟩ := sab_comp_exists n' M.m2 _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T'.V T'.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hψ])
    refine ⟨⟨ψ.comp M.ρ, ?_, G, t', N, N', m1, m2, ?_, ?_⟩, n, n', h1, h2.trans hk⟩
    · rw [← RingHom.comp_assoc, hψ, RingHom.comp_assoc, M.hρ, RingHom.comp_assoc]
    · rw [h1, hN', M.h1, Category.assoc]
    · rw [hN, hN', ← Category.assoc, h2, hk, Category.assoc, M.h2, Category.assoc]

end GlobalTheory.LamT
