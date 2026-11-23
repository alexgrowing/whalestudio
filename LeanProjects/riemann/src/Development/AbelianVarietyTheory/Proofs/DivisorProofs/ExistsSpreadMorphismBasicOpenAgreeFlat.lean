import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_spread_basicOpen_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp R) (B Z B₀ : Scheme.{0})
    (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → QuasiCompact pB → QuasiSeparated pB → IsSeparated pZ →
    LocallyOfFinitePresentation pZ → ∀ (φ₀ : B₀ ⟶ B) (u₀ : B₀ ⟶ Z), Flat φ₀ → u₀ ≫ pZ = φ₀ ≫ pB →
    ∀ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
      t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u) →
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) →
      ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y),
        t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  intro R _ _ x B Z B₀ pB pZ hfl hqc hqs hsep hlfp φ₀ u₀ hφfl hu₀ u hu hagree
  haveI := hfl; haveI := hqc; haveI := hqs; haveI := hsep; haveI := hlfp; haveI := hφfl
  obtain ⟨V, hxV, -, w, g₀, hw, hwg, hg₀⟩ :=
    GlobalTheory.StalkLimit.exists_spread (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x)) pZ u hu
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open (a := x) hxV V.isOpen

  have key : pullback.fst φ₀ (pullback.fst pB V.ι) ≫ u₀ = pullback.snd φ₀ (pullback.fst pB V.ι) ≫ g₀ := by
    let qN : pullback φ₀ (pullback.fst pB V.ι) ⟶ Sp R := pullback.fst _ _ ≫ φ₀ ≫ pB
    haveI : Flat qN := inferInstance
    haveI : IsDominant ((Sp R).fromSpecStalk x) := by
      refine ⟨Dense.mono (s₁ := {genericPoint (Sp R)}) ?_ ?_⟩
      · rw [Set.singleton_subset_iff, Scheme.range_fromSpecStalk]
        exact genericPoint_specializes x
      · rw [dense_iff_closure_eq]
        exact (genericPoint_spec (Sp R)).trans (by simp)
    haveI : IsSchemeTheoreticallyDominant ((Sp R).fromSpecStalk x) := .of_isDominant _
    have hPB := IsPullback.of_hasPullback qN ((Sp R).fromSpecStalk x)
    haveI : IsSchemeTheoreticallyDominant (pullback.fst qN ((Sp R).fromSpecStalk x)) :=
      .of_isPullback hPB.flip
    refine ext_of_schDom pZ ?_ (pullback.fst qN ((Sp R).fromSpecStalk x)) ?_
    · simp only [Category.assoc, hu₀, hg₀]
      rw [pullback.condition_assoc]
    · let m : pullback qN ((Sp R).fromSpecStalk x) ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
        pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _ ≫ φ₀) (pullback.snd _ _)
          (by rw [Category.assoc, Category.assoc]; exact pullback.condition)
      have hm : m ≫ pullback.fst pB ((Sp R).fromSpecStalk x) =
          pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.fst φ₀ (pullback.fst pB V.ι) ≫ φ₀ :=
        pullback.lift_fst _ _ _
      have h1 := hagree _ (pullback.fst _ _ ≫ pullback.fst _ _) m ((Category.assoc _ _ _).trans hm.symm)
      have h2 : m ≫ w = pullback.fst qN ((Sp R).fromSpecStalk x) ≫ pullback.snd φ₀ (pullback.fst pB V.ι) := by
        rw [← cancel_mono (pullback.fst pB V.ι)]
        rw [Category.assoc, hw, hm, Category.assoc, pullback.condition]
      rw [← Category.assoc, h1, ← hwg, ← Category.assoc, h2, Category.assoc]
  refine ⟨g, hxg, fun Y a ha => ?_⟩
  have hrange : Set.range (a ≫ pB) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hgV (ha y)
  let k : Y ⟶ pullback pB V.ι :=
    pullback.lift a (IsOpenImmersion.lift V.ι (a ≫ pB) hrange) (IsOpenImmersion.lift_fac _ _ _).symm
  refine ⟨k ≫ g₀, ?_, fun T t₀ t ht => ?_⟩
  · rw [Category.assoc, hg₀, pullback.lift_fst_assoc]
  · have := pullback.lift t₀ (t ≫ k) (by rw [ht, Category.assoc, pullback.lift_fst]) ≫= key
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at this
    exact this

end GlobalTheory.Desc
