import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
