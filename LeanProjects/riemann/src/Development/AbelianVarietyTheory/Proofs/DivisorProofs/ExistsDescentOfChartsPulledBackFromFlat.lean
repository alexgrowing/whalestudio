import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOverlapEqPreimageOpenOfFibreStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartTransitionMapsDescendOverlapsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOverlapDiagonalAndTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentTransitionDiagonalInclusionOverBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedChartTransitionsCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueCopiesOfSchemeCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGlueMapsOpenCoverSameSourceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfIsPullbackOnOpenCoverTargetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentInvariantOfChartwiseProjectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ChartDescent

theorem key_move : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, e j ≫ f = pullback.snd _ _) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) := by
  intro B S X π f Φ U J e hf hc i j T w₁ w₂ h₁ hw hh
  have hπ : w₁ ≫ pullback.snd U.hom π ≫ π = w₂ ≫ pullback.snd U.hom π ≫ π := by
    rw [← pullback.condition, reassoc_of% hw]
  have hs1 : h₁ ≫ pullback.snd U.hom π = w₁ ≫ pullback.snd U.hom π := by
    simpa only [Category.assoc, hf] using congrArg (· ≫ f) hh
  let s : T ⟶ pullback π π := pullback.lift (w₁ ≫ pullback.snd _ _) (w₂ ≫ pullback.snd _ _)
    (by simpa only [Category.assoc] using hπ)
  have hs₁ : s ≫ pullback.fst π π = w₁ ≫ pullback.snd _ _ := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd π π = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  let z : T ⟶ pullback f (pullback.fst π π) := pullback.lift (w₁ ≫ e i) s
    (by rw [hs₁, Category.assoc, hf])
  have hz₁ : z ≫ pullback.fst _ _ = w₁ ≫ e i := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  have h1 := hc i T w₁ w₂ s hw hs₁.symm hs₂.symm z hz₁ hz₂
  let y₂ : T ⟶ pullback U.hom π := pullback.lift (h₁ ≫ pullback.fst _ _) (w₂ ≫ pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, reassoc_of% hs1, Category.assoc, hπ])
  have hy₁ : y₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hy₂ : y₂ ≫ pullback.snd _ _ = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have h2 := hc j T h₁ y₂ s hy₁.symm (hs1.trans hs₁.symm) (hy₂.trans hs₂.symm) z (hz₁.trans hh.symm) hz₂
  exact ⟨y₂, by rw [← h2, h1], hy₁⟩

theorem cocycle_facts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ i, τ i i = (V i i).ι) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) ∧ (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨h1, h2⟩ := GlobalTheory.T.glue_overlap_diagonal_top_and_cocycle (Sp R) S X π hπs U J e he V τ hV hτ
  obtain ⟨h3, h4⟩ := GlobalTheory.T.descent_transition_diagonal_inclusion_over_base R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  exact ⟨h1, h3, h2, GlobalTheory.T.descended_chart_transitions_cocycle R S X π hπp hπs hS U hU J e he V τ hV hτ, h4⟩

theorem exists_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)), Φ ≫ pullback.snd _ _ = pullback.snd _ _ → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → ∃ (G : Over (Sp R)) (β : X ⟶ G.left) (ψ : J → (U.left ⟶ G.left)), (∀ j, IsOpenImmersion (ψ j) ∧ ψ j ≫ G.hom = U.hom ∧ e j ≫ β = pullback.fst _ _ ≫ ψ j) ∧ (∀ g : G.left, ∃ j, g ∈ Set.range (ψ j)) ∧ IsPullback β f G.hom π ∧ pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro R _ _ _ _ S X π f hπp hπs hS Φ hΦ U hU J e he hef hcov hc
  have hK := key_move (Sp R) S X π f Φ U J e hef hc
  choose V hV using GlobalTheory.T.chartOverlap_eq_preimage_open_of_fibre_stable (Sp R) S X π U J e hπp hπs he hK
  choose τ hτ using fun i j => GlobalTheory.T.chart_transition_maps_descend_overlaps R S X π hπp hπs hS U hU J e he hK i j (V i j) (hV i j)
  obtain ⟨hVt, hτi, hland, hcoc, hτR⟩ := cocycle_facts R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨G₀, ψ, hψo, hψc, hψp, hψd⟩ := GlobalTheory.T.exists_glue_copies_of_scheme_cocycle U.left J V τ hVt hτi hland hcoc
  obtain ⟨F, hF⟩ := hψd (Sp R) (fun _ => U.hom) (fun i j => (hτR i j).symm)
  have hcomp : ∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π), a ≫ e i = b ≫ e j →
      a ≫ pullback.fst _ _ ≫ ψ i = b ≫ pullback.fst _ _ ≫ ψ j := by
    intro i j T a b hab
    have hr : Set.range (a ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      refine (hV i j (a t)).2 ⟨b t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
    have hv : IsOpenImmersion.lift (V i j).ι (a ≫ pullback.fst _ _) hr ≫ (V i j).ι =
        a ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
    rw [← Category.assoc, ← hv, Category.assoc, (hψp i j).w, ← Category.assoc,
      hτ i j T a b _ hab hv, Category.assoc]
  obtain ⟨β, hβ, -⟩ := GlobalTheory.T.existsUnique_glue_maps_openCover_same_source X G₀ (pullback U.hom π) J e (fun j => pullback.fst _ _ ≫ ψ j) he hcov hcomp
  have hw : β ≫ F = f ≫ π := by
    obtain ⟨gg, -, hgg⟩ := GlobalTheory.T.existsUnique_glue_maps_openCover_same_source X (Sp R) (pullback U.hom π) J e (fun _ => pullback.snd _ _ ≫ π) he hcov
      (fun i j T a b hab => by
        have h1 : a ≫ pullback.snd U.hom π = b ≫ pullback.snd U.hom π := by
          simpa only [Category.assoc, hef] using congrArg (· ≫ f) hab
        rw [reassoc_of% h1])
    rw [hgg (β ≫ F) (fun j => by rw [reassoc_of% hβ j, hF j, pullback.condition]),
      hgg (f ≫ π) (fun j => by rw [reassoc_of% hef j])]
  refine ⟨Over.mk F, β, ψ, fun j => ⟨hψo j, hF j, hβ j⟩, hψc, ?_, ?_⟩
  · refine GlobalTheory.T.isPullback_of_isPullback_on_openCover_target X G₀ S (Sp R) β f F π hw J (fun _ => U.left) (fun _ => pullback U.hom π) ψ e
      (fun _ => pullback.fst _ _) (fun _ => pullback.snd _ _) hψo hψc he
      (fun j => by rw [hF j]; exact IsPullback.of_hasPullback U.hom π) hβ hef ?_
    rintro j x ⟨y, hy⟩
    obtain ⟨i, a, rfl⟩ := hcov x
    have hxa : β (e i a) = ψ i (pullback.fst U.hom π a) := by
      rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hψp i j) (pullback.fst U.hom π a) y
      (by rw [← hxa, hy])
    have ha : pullback.fst U.hom π a ∈ V i j := by
      have h0 : (V i j).ι z ∈ Set.range (V i j).ι := ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι] at h0; rwa [← hz]
    exact (hV i j a).1 ha
  · exact GlobalTheory.T.descentInvariant_of_chartwise_projection (Sp R) S X G₀ π f Φ U J e ψ β he hcov hef hβ hc

end GlobalTheory.Mum.ChartDescent
