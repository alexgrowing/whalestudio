import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChartFin
import Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
import Development.WeilBound.CoreStatements.HodgeTatePoints.RedOmHTBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.DualUnique
import Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj
import Development.WeilBound.CoreStatements.HodgeTatePoints.GdSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Ge

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  classical
  haveI := Module.finitePresentation_of_projective A M
  let S := nonZeroDivisors A
  let F := Localization S
  let f := LocalizedModule.mkLinearMap S M
  let g := Algebra.linearMap A F
  have e1 : finrank A (Module.Dual A M) = finrank A (LocalizedModule S M →ₗ[F] F) :=
    (IsLocalizedModule.finrank_eq S (IsLocalizedModule.mapExtendScalars S f g F) le_rfl).symm
  rw [e1, ← IsLocalization.finrank_eq F S le_rfl, Subspace.dual_finrank_eq,
    IsLocalization.finrank_eq F S le_rfl, IsLocalizedModule.finrank_eq S f le_rfl]

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chart_sequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hκ htest hproj'
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right κ _) hκ
  have h1 := PositivityTheory.HtPt.Gc.chart_ii A K E c hc p R N Ω D κ hκR hproj' htest
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hint : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hr⟩ :=
    PositivityTheory.HtPt.Ga.dual_map A K hinj E c hc p R N Ω D κ σ d m hint hd hκ h1.2 hP2
  obtain ⟨-, -, hsurj⟩ := PositivityTheory.HtPt.Ga.q_surj A K hinj E c hc p R N Ω D κ σ m (hint σ) hκ h1.2
  have hcz := PositivityTheory.HtPt.Gd.chart_comp_zero A K E c hc p R N Ω D κ σ d d' m i hκ hd hd' h1.2
    hP1 hP2 htest hi
  refine ⟨i, hi, hr i hi, ?_, hsurj⟩
  intro x
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu⟩ := hu
      refine ⟨0, (↑u⁻¹ : A) ^ m • x, ?_⟩
      rw [map_zero, zero_add, smul_smul, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D σ)
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) :=
        Module.Finite.iff_fg.mpr (PositivityTheory.HtPt.Gd.omHT_fg D _)
      let q' : (Fin N → A) →ₗ[A] D.omHT σ :=
        (qLin D σ).codRestrict (D.omHT σ) (PositivityTheory.HtPt.Ga.q_mem D σ)
      have hrank : finrank A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) +
          finrank A (D.omHT σ) = N := by
        rw [finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom)), add_comm]
        exact PositivityTheory.HtPt.Gb.chart_rank A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 htest
      obtain ⟨rr, hrr⟩ := hr i hi
      obtain ⟨w, x', hx⟩ := PositivityTheory.HtPt.Gd.split_exact A
        (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m) i rr q' hrank hrr
        (fun z => by
          obtain ⟨x0, y', hy', h⟩ := hsurj z.1 z.2
          exact ⟨x0, ⟨y', hy'⟩, Subtype.ext h⟩)
        (fun w => by
          obtain ⟨y0, hy0, h0⟩ := hcz w
          exact ⟨⟨y0, hy0⟩, Subtype.ext h0⟩)
        x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      exact ⟨w, x', hx⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y0, hy0, h0⟩ := hcz w
    refine ⟨y0 + D.q σ x', (D.omHT σ).add_mem hy0 (PositivityTheory.HtPt.Ga.q_mem D σ x'), ?_⟩
    have hq : ∀ z, D.q σ z = qLin D σ z := fun _ => rfl
    rw [hq, map_add, map_smul, ← hq, ← hq, h0, smul_add]
    all_goals rfl

end PositivityTheory.HtPt.Ge
