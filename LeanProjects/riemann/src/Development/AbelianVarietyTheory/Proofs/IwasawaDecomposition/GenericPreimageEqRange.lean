import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem preimage_range_jQ_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (X : Model Xo c β) (Y : Model Xo c (RingHom.id c.F))
    (ρ : gen Y ⟶ gen X), Y.jQ ≫ ρ = X.jQ → ρ ⁻¹' Set.range X.jQ = Set.range Y.jQ := by
  intro E _ _ _ H D l Xo c O _ β X Y ρ hρ

  have hsY : IsSeparated Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have : IsProper (PSpace.str c.F N) := isProper_str _ N
    rw [← hs]; infer_instance
  have hsep : IsSeparated (terminal.from (gen Y)) := by
    have : terminal.from (gen Y) = pullback.snd Y.s (spMap (RingHom.id c.F)) ≫ terminal.from _ :=
      terminal.hom_ext _ _
    rw [this]; infer_instance
  have hρsep : IsSeparated ρ := by
    have : ρ ≫ terminal.from (gen X) = terminal.from (gen Y) := terminal.hom_ext _ _
    haveI : IsSeparated (ρ ≫ terminal.from (gen X)) := by rw [this]; exact hsep
    exact IsSeparated.of_comp ρ (terminal.from (gen X))
  haveI := X.jQ_open
  haveI := Y.jQ_open
  let V : (gen Y).Opens := ρ ⁻¹ᵁ X.jQ.opensRange
  have hV : (V : Set (gen Y)) = ρ ⁻¹' Set.range X.jQ := rfl
  have hAV : Set.range Y.jQ ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hV]
    rintro _ ⟨z, rfl⟩
    exact ⟨z, by rw [← hρ]; rfl⟩
  let s : Xo.XF c ⟶ V.toScheme := IsOpenImmersion.lift V.ι Y.jQ hAV
  have hs : s ≫ V.ι = Y.jQ := IsOpenImmersion.lift_fac _ _ _
  have hBV : Set.range (V.ι ≫ ρ) ⊆ Set.range X.jQ := by
    rintro _ ⟨w, rfl⟩
    have hw : V.ι w ∈ (V : Set (gen Y)) := by rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    rw [hV] at hw
    exact hw
  let r : V.toScheme ⟶ Xo.XF c := IsOpenImmersion.lift X.jQ (V.ι ≫ ρ) hBV
  have hr : r ≫ X.jQ = V.ι ≫ ρ := IsOpenImmersion.lift_fac _ _ _
  have hsr : s ≫ r = 𝟙 _ := by
    rw [← cancel_mono X.jQ, Category.assoc, hr, ← Category.assoc, hs, hρ, Category.id_comp]
  haveI : IsSeparated (r ≫ X.jQ) := by rw [hr]; infer_instance
  haveI : IsSeparated r := IsSeparated.of_comp r X.jQ
  haveI : IsClosedImmersion (s ≫ r) := by rw [hsr]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s r
  have hcl : IsClosed (Set.range s) := s.isClosedEmbedding.isClosed_range
  have hpre : V.ι ⁻¹' Set.range Y.jQ = Set.range s := by
    ext x; constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← hz, ← hs]; rfl
    · rintro ⟨z, rfl⟩; exact ⟨z, by rw [← hs]; rfl⟩
  have hd : Dense (Set.range s) := by
    rw [← hpre]; exact Y.jQ_dense.preimage V.ι.isOpenEmbedding.isOpenMap
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨w, rfl⟩ : v ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι, hV]; exact hv
    have hw : w ∈ Set.range s := by
      rw [← hcl.closure_eq, hd.closure_eq]; trivial
    rw [← hpre] at hw
    exact hw
  · exact hAV.trans (by rw [Scheme.Opens.range_ι, hV])
end GlobalTheory.TorRef
