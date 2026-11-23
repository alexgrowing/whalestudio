import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isOpen_punct (n a : ℕ) (ρ : ℝ) : IsOpen (punct n a ρ) := by
  have h : punct n a ρ = Metric.ball 0 ρ ∩ ⋂ i : Fin n, {z : Fin n → ℂ | (i : ℕ) < a → z i ≠ 0} := by
    ext z
    simp only [punct, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => ?_)
  by_cases hi : (i : ℕ) < a
  · simp only [hi, true_implies]
    exact isOpen_ne_fun (continuous_apply i) continuous_const
  · simp [hi]

theorem isHolTo_of_comp_openImmersion {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {X Y : Scheme.{0}}
    (j : X ⟶ Y) [IsOpenImmersion j] {B : Set W} {y : W → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ j) : IsHolTo B y := by
  intro U f
  have hpre : ∀ x : Sp ℂ ⟶ X, (x ≫ j) ⁻¹ᵁ (j ''ᵁ U) = x ⁻¹ᵁ U := by
    intro x
    ext p
    simp
  have key : ∀ (x : Sp ℂ ⟶ X) (h1 : ⊤ ≤ (x ≫ j) ⁻¹ᵁ (j ''ᵁ U)) (h2 : ⊤ ≤ x ⁻¹ᵁ U),
      valAt (x ≫ j) (j ''ᵁ U) h1 ((j.appIso U).inv f) = valAt x U h2 f := by
    intro x h1 h2
    have e : (j.appIso U).inv ≫ (x ≫ j).appLE (j ''ᵁ U) ⊤ h1 = x.appLE U ⊤ h2 := by
      rw [← Scheme.Hom.appLE_comp_appLE x j (j ''ᵁ U) U ⊤ (j.preimage_image_eq U).ge h2]
      rw [← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simp
    unfold valAt
    rw [← e]
    rfl
  have hval : ∀ b, valAt' (y b ≫ j) (j ''ᵁ U) ((j.appIso U).inv f) = valAt' (y b) U f := by
    intro b
    unfold valAt'
    by_cases hb : ⊤ ≤ y b ⁻¹ᵁ U
    · have hb' : ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dif_pos hb, dif_pos hb']
      exact key _ hb' hb
    · have hb' : ¬ ⊤ ≤ (y b ≫ j) ⁻¹ᵁ (j ''ᵁ U) := by rw [hpre]; exact hb
      rw [dif_neg hb, dif_neg hb']
  obtain ⟨ho, hd⟩ := h (j ''ᵁ U) ((j.appIso U).inv f)
  simp only [hpre] at ho hd
  exact ⟨ho, by simpa only [hval] using hd⟩

theorem isHolTo_pt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), IsHolTo (punct n a 1) C.pt := by
  intro E _ _ _ H D l Xo σ n a C
  haveI := C.j_open
  apply isHolTo_of_comp_openImmersion C.j
  have hB : IsOpen (punct n a 1) := isOpen_punct n a 1
  have hsub : punct n a 1 ⊆ Metric.ball 0 1 := fun z hz => hz.1
  have h0 : IsHolTo (punct n a 1) fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (C.ψ z) :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hB fun r => (C.hol.2 r).mono hsub
  exact GlobalTheory.FiniteOrderConst.isHolTo_of_eqOn h0 fun z hz => (C.pt_eq z hz).1

end GlobalTheory.CompanionTheory.Ar.Flat
