import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_affine_le_of_cover {X : Scheme.{0}} {N : Type} (𝒰 : N → X.Opens) (h𝒰 : ⨆ i, 𝒰 i = ⊤) (e : Sp ℂ ⟶ X) :
    ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ⊤ ≤ e ⁻¹ᵁ U := by
  have pt : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have h1 : e pt ∈ ⨆ i, 𝒰 i := by rw [h𝒰]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h1
  obtain ⟨U, hU, hx, hle⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hi
  refine ⟨i, U, hU, hle, fun y _ ↦ ?_⟩
  obtain rfl : y = pt := Subsingleton.elim _ _
  exact hx

theorem exists_charts_subordinate : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  intro I _ g Λ _ F B _ X s σ u hX N 𝒰 h𝒰
  let Q : Opens (Tot I g) → Prop := fun W ↦ ∃ i U, IsAffineOpen U ∧ U ≤ 𝒰 i ∧ ∀ p ∈ W, ⊤ ≤ u.E p ⁻¹ᵁ U
  obtain ⟨r, hr, hx⟩ := GlobalTheory.T.exists_analyticChartsRealization_of_affine u hX (Charts.std F Q) fun k ↦ by
    obtain ⟨i, U, h1, -, h3⟩ := k.2.2
    exact ⟨U, h1, h3⟩
  refine ⟨Charts.std F Q, r, fun k ↦ k.2.2.choose, ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩, fun l k' ↦ ?_, hr,
    fun k ↦ ?_⟩
  · obtain ⟨i, U, hU, hle, hp'⟩ := exists_affine_le_of_cover 𝒰 h𝒰 (u.E p)
    exact ⟨⟨⟨_, (u.hol U 0).1⟩, fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ hq.2⟩, hp, hp'⟩
  · have hc : ContinuousOn (F.shift l) (k₁.1 : Set (Tot I g)) := (F.shift_analytic l k₁.2.1).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k₁.2.2
    refine ⟨⟨⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' k₂.1, hc.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩,
      fun q hq ↦ k₁.2.1 q hq.1, i, U, hU, hle, fun q hq ↦ hW q hq.1⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]; exact hq.1
  · have hc : ContinuousOn (F.shift (-l)) (F.tot : Set (Tot I g)) := (F.shift_analytic (-l) fun _ h ↦ h).continuousOn
    obtain ⟨i, U, hU, hle, hW⟩ := k'.2.2
    refine ⟨⟨⟨(F.tot : Set (Tot I g)) ∩ F.shift (-l) ⁻¹' k'.1, hc.isOpen_inter_preimage F.tot.isOpen k'.1.isOpen⟩,
      fun q hq ↦ hq.1, i, U, hU, hle, fun q hq ↦ ?_⟩, fun q hq ↦ ⟨k'.2.1 q hq, ?_⟩, fun q hq ↦ hq.2⟩
    · rw [← u.per (-l) q hq.1]
      exact hW _ hq.2
    · change F.shift (-l) (F.shift l q) ∈ k'.1
      rwa [← F.shift_add, neg_add_cancel, F.shift_zero]
  · obtain ⟨U, hU, hle, hW⟩ := k.2.2.choose_spec
    exact fun y hy ↦ hle (hx k U hU hW hy)

end GlobalTheory.AnPer
