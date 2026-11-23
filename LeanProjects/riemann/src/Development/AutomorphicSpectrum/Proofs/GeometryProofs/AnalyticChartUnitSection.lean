import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_hChart_of_extendsUnitAt : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  intro X s Ω _ ξ W U N F T t v d B Y b₁ hξ hY hb₁ hN hNU hW hv hg hT hE
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap]
  obtain ⟨ε, h', hε, hd, h0, hrel⟩ := hE d B Y hY.isOpen hY.hol
    (fun b hb => (hY.isOver b hb).trans hid.symm) b₁ hb₁ rfl
  have hopen : IsOpen (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) :=
    hd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hB₂ : IsOpen (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) := hY.isOpen.inter hopen
  have hsub : B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) ⊆ B := Set.inter_subset_left
  have htop : ∀ b ∈ B, ⊤ ≤ Y b ⁻¹ᵁ N := fun b hb => (top_le_iff_centre _ _).2 (hN b hb).1
  refine ⟨B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ), fun b => h' b * valAt' (Y b) N v,
    ⟨hb₁, Metric.mem_ball_self hε, h0⟩, ?_⟩
  refine
    { chart := hY.mono hB₂ hsub
      inU := fun b hb => hNU (hN b hb.1).1
      cpt := fun b hb => (hN b hb.1).2
      dense := fun O oO sO nO => hW O oO (sO.trans hsub) nO
      hol := ?_
      ne := ?_
      rel := ?_ }
  · refine DifferentiableOn.mul (hd.mono fun b hb => hb.2.1) ?_
    exact (hY.hol N v).2.mono fun b hb => ⟨hb.1, htop b hb.1⟩
  · intro b hb
    refine mul_ne_zero hb.2.2 ?_
    intro hz
    obtain ⟨u, rfl⟩ := hv
    have e := valAt'_mul (Y b) N u.val u⁻¹.val
    rw [Units.mul_inv, valAt'_one (Y b) N (htop b hb.1), hz, zero_mul] at e
    exact one_ne_zero e
  · intro b hb hWb r hr
    have e₁ : ValAt ξ (Y b) (t / T) (valAt' (Y b) N v) :=
      ValAt.of_section (hN b hb.1).1 (hN b hb.1).2 (hg _ _ _)
    have e₂ : ValAt ξ (Y b) t (valAt' (Y b) N v * r) := by
      have := ValAt.mul e₁ hr
      rwa [div_mul_cancel₀ _ hT] at this
    rw [hrel b ⟨hb.1, hb.2.1⟩ ((top_le_iff_centre _ _).2 hWb) _ e₂, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
