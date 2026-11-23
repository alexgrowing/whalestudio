import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem exists_lift_of_mem_range {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (x : Sp ℂ ⟶ X)
    (p : Sp ℂ) (hp : x p ∈ Set.range i) : ∃ t : Sp ℂ ⟶ Z, t ≫ i = x := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hs : Surjective (pullback.snd i x) :=
    ⟨fun q => ⟨w, by rw [hw]; exact Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i x)
  exact ⟨inv (pullback.snd i x) ≫ pullback.fst i x, by simp [pullback.condition]⟩

theorem one_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem mem_per_of_frequently : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  intro R _ G _ _ g n M B ψ e hsep hψ b₀ hb₀ s hs hfr
  haveI := hsep
  by_contra hne
  have hid : η[G].left ≫ G.hom = 𝟙 _ := Over.w _
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp _ G.hom
  let V : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, hη.base_closed.isClosed_range.isOpen_compl⟩
  have hV₀ : ⊤ ≤ (e.ex b₀ (s b₀)).left ⁻¹ᵁ V := by
    intro p _
    show (e.ex b₀ (s b₀)).left p ∉ Set.range η[G].left
    intro hp
    obtain ⟨t, ht⟩ := exists_lift_of_mem_range η[G].left (e.ex b₀ (s b₀)).left p hp
    apply hne
    show e.ex b₀ (s b₀) = 1
    apply Over.OverMorphism.ext
    have h1 : t = spMap (ψ b₀) := by
      have h2 := Over.w (e.ex b₀ (s b₀))
      have h4 : (t ≫ η[G].left) ≫ G.hom = spMap (ψ b₀) := by rw [ht]; exact h2
      rw [Category.assoc, hid] at h4
      exact h4
    rw [one_left_eq, ← ht, h1]
    rfl
  have hopen := (e.hol V 0).1
  have hmem : (b₀, s b₀) ∈ {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ V} :=
    ⟨⟨hb₀, trivial⟩, hV₀⟩
  have hcont : ContinuousAt (fun b => (b, s b)) b₀ := continuousAt_id.prodMk hs
  have hev := hcont.eventually (hopen.mem_nhds hmem)
  obtain ⟨b, ⟨-, hper⟩, -, hb⟩ := (hfr.and_eventually hev).exists
  have hper' : e.ex b (s b) = 1 := hper
  have hb' : ⊤ ≤ (e.ex b (s b)).left ⁻¹ᵁ V := hb
  rw [hper'] at hb'
  let p : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have hp : (1 : Over.mk (spMap (ψ b)) ⟶ G).left p ∉ Set.range η[G].left := hb' (show p ∈ ⊤ from trivial)
  apply hp
  rw [one_left_eq]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat
