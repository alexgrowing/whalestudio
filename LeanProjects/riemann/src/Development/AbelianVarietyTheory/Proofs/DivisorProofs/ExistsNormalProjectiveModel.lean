import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsProjOverIsPullbackOfIsLocalization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CommonModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.CommonModel.isProper_of_isProjOver {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s) : IsProper s := by
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace in

theorem _root_.GlobalTheory.CommonModel.exists_common {R : Type} [CommRing R] {Y W₀ : Scheme.{0}}
    (s₀ : W₀ ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s₀) (i₀ : Y ⟶ W₀)
    {ι : Type} (P : ι → Scheme.{0}) (p : ∀ i, P i ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (f : ∀ i, Y ⟶ P i)
    (hp : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (p i))
    (hf : ∀ i, f i ≫ p i = i₀ ≫ s₀) (S : Finset ι) :
    ∃ (W : Scheme.{0}) (h : Y ⟶ W) (r : W ⟶ W₀), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (r ≫ s₀) ∧ h ≫ r = i₀ ∧
      ∀ i ∈ S, ∃ g : W ⟶ P i, h ≫ g = f i ∧ g ≫ p i = r ≫ s₀ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨W₀, i₀, 𝟙 W₀, by simpa using hs₀, by simp, by simp⟩
  | insert j S _ ih =>
    obtain ⟨W, h, r, hr, hhr, hg⟩ := ih
    have hc : h ≫ (r ≫ s₀) = f j ≫ p j := by
      rw [← Category.assoc, hhr, hf]
    refine ⟨pullback (r ≫ s₀) (p j), pullback.lift h (f j) hc, pullback.fst _ _ ≫ r, ?_, ?_, ?_⟩
    · rw [Category.assoc]
      exact _root_.GlobalTheory.ProjSpace.isProjOver_pullback hr (hp j)
    · rw [← Category.assoc, pullback.lift_fst, hhr]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩
        rw [Category.assoc, ← pullback.condition]
      · obtain ⟨g, hg₁, hg₂⟩ := hg i hi
        refine ⟨pullback.fst _ _ ≫ g, ?_, ?_⟩
        · rw [← Category.assoc, pullback.lift_fst, hg₁]
        · rw [Category.assoc, hg₂, Category.assoc]

end GlobalTheory.CommonModel
