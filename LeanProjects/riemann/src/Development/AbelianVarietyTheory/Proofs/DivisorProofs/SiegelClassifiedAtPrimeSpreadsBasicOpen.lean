import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegSpread

theorem spread_point : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := GlobalTheory.T.exists_away_spread_point_localization_atPrime

theorem spread_iso : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := GlobalTheory.T.exists_spread_of_pullbacks_alt

theorem spMap_comp_eq {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (a : A →+* C) (b : C →+* D) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem classified_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  intro g n hg hn hodd F R _ _ β c 𝔭 _ hc H
  obtain ⟨c₀, hc₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _)
    (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))
    (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl (by rw [spMap_comp_eq, spMap_comp_eq, RingHom.comp_id])).1 c
  obtain ⟨f₀, hf₀s, hf₀⟩ := H c₀ hc₀
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : LocallyOfFinitePresentation F.s := inferInstance
  obtain ⟨r₀, hr₀, ι₀, f₁, hι₀, hf₁s, hf₁⟩ := spread_point (cycAway n) F.X F.s R β 𝔭 f₀ hf₀s
  obtain ⟨r, hr, κ, d', hκ, hd'c, hd'u⟩ := spread_iso g n (cycAway n) (zetaAway n) R β 𝔭 c F.X F.s F.univ r₀ ι₀ f₁ c₀
    hr₀ hι₀ hf₁s hc₀ (hf₁ ▸ hf₀)
  refine ⟨r, hr, fun c' hc' => ⟨spMap κ ≫ f₁, ?_, ?_⟩⟩
  · rw [Category.assoc, hf₁s, spMap_comp_eq, ← RingHom.comp_assoc, hκ]
  · have h₁ : SiegPB c' c (𝟙 _ ≫ spMap (algebraMap R (Localization.Away r))) := by rwa [Category.id_comp]
    have h₂ := GlobalTheory.SiegelPullComp.pb_cancel hd'c h₁
    have h₃ := GlobalTheory.SiegelPullComp.pb_comp hd'u h₂
    rwa [Category.id_comp] at h₃

end GlobalTheory.SiegSpread
