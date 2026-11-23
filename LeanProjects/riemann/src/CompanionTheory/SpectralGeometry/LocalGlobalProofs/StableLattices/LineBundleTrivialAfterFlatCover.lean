import Mathlib
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigCover

theorem exists_gen_of_chart {Y P : Scheme.{0}} {M : LB P} (hM : M.IsLB) (f : Y ⟶ P) (i : M.ι)
    (hf : ∀ y, f y ∈ M.U i) : ∃ t : LB.Gen (M.pull f), t.IsGen := by
  have le : ∀ J : PUnit → M.ι, LB.wchart M (K := PUnit) (fun _ => f) J ≤ f ⁻¹ᵁ (M.U (J PUnit.unit) ⊓ M.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (M.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have hJ : f y ∈ M.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : f y ∈ M.U (J' PUnit.unit) := mem_pull.1 hy.2
  have key : ∀ (K : PUnit → M.ι) (h : f y ∈ M.U (K PUnit.unit)) (hk : y ∈ LB.wchart M (K := PUnit) (fun _ => f) K),
      gm (𝟙 Y) y _ (res (le K) (pullU f _ (M.g (K PUnit.unit) i))) =
        gm (𝟙 Y ≫ f) y _ (M.g (K PUnit.unit) i) := fun K h hk =>
    (gm_res _ y (le K) hk _).trans (gm_pull (𝟙 Y) f y (M.U (K PUnit.unit) ⊓ M.U i) (show f y ∈ _ from ⟨h, hf y⟩) _)
  have e : gm (𝟙 Y) y _ ((M.pull f).g J J') = gm (𝟙 Y ≫ f) y _ (M.g (J PUnit.unit) (J' PUnit.unit)) := by
    show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (M.g (J PUnit.unit) (J' PUnit.unit)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res _ y _ hy _).trans (gm_pull (𝟙 Y) f y (M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit)) (show f y ∈ _ from ⟨hJ, hJ'⟩) _)
  rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
  exact (key J hJ hy.1).trans ((gm_cocycle hM (𝟙 Y ≫ f) y hJ hJ' (hf y)).symm.trans
    (congrArg₂ (· * ·) e.symm (key J' hJ' hy.2).symm))

theorem exists_flat_cover_triv : ∀ {P : Scheme.{0}} (M : LB P), M.IsLB → ∃ (Z : Scheme.{0}) (g : Z ⟶ P),
    Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g ∧ Triv (M.pull g) := by
  intro P M hM
  let D : M.ι → Scheme.{0} := fun i => (M.U i).toScheme
  let g : ∐ D ⟶ P := Sigma.desc fun i => (M.U i).ι
  have hι : ∀ i, Sigma.ι D i ≫ g = (M.U i).ι := fun i => Sigma.ι_desc _ i
  refine ⟨∐ D, g, ?_, ?_, ?_, ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
    have hf : ∀ i : M.ι, Flat (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover D) hf
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    have hf : ∀ i : M.ι, LocallyOfFinitePresentation (Sigma.ι D i ≫ g) := fun i => by rw [hι]; infer_instance
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover D) hf
  · refine ⟨fun x => ?_⟩
    obtain ⟨i, hi⟩ := exists_chart hM x
    let x' : D i := ⟨x, hi⟩
    refine ⟨Sigma.ι D i x', ?_⟩
    have e : (Sigma.ι D i ≫ g) x' = x := by rw [hι]; rfl
    exact e
  · let W : M.ι → (∐ D).Opens := fun i => (Sigma.ι D i).opensRange
    have hW : ∀ y, ∃ s, y ∈ W s := fun y => by
      obtain ⟨i, x, rfl⟩ := (sigmaOpenCover D).exists_eq y
      exact ⟨i, x, rfl⟩
    have hg : ∀ s, ∃ t : LB.Gen (M.pull ((W s).ι ≫ g)), t.IsGen := fun s => by
      refine exists_gen_of_chart hM _ s fun y => ?_
      obtain ⟨x, hx⟩ : ((W s).ι y) ∈ Set.range (Sigma.ι D s) := y.2
      have : ((W s).ι ≫ g) y = (M.U s).ι x := by
        rw [← hι s, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
      rw [this]
      exact x.2
    choose t ht using hg
    obtain ⟨u, hu, -⟩ := glue_gen hM (K := PUnit) (fun _ => g) (fun _ => 1) W hW t ht
      (fun s s' Z r r' z J _ hr => by
        by_cases e : s = s'
        · subst e
          have : r = r' := (cancel_mono (W s).ι).1 hr
          rw [this]
        · exfalso
          have mem : ∀ (a : M.ι) (q : Z ⟶ (W a).toScheme), (q ≫ (W a).ι) z ∈ W a := fun a q => (q z).2
          have m₁ := mem s r
          have m₂ : (r ≫ (W s).ι) z ∈ W s' := hr ▸ mem s' r'
          have d : W s ⊓ W s' = ⊥ := disjoint_iff.1 (disjoint_opensRange_sigmaι D s s' e)
          have hx : (r ≫ (W s).ι) z ∈ W s ⊓ W s' := ⟨m₁, m₂⟩
          rw [d] at hx
          exact hx)
    exact ⟨u, hu⟩

end GlobalTheory.CompanionTheory.RigCover
