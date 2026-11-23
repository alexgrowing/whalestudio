import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairingStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartTestPointStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitPStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBoundStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibilityStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 (IsFractionRing.injective A K)
  rw [← (TensorProduct.isBaseChange A (Module.Dual A M) K).finrank_eq,
    ← (TensorProduct.isBaseChange A M K).finrank_eq]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange A M M K LinearMap.id).1

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

theorem chartSequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hdiv hT hproj
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right _ _) hdiv
  have h1 := GlobalTheory.T.hodge_tate_chart_test_point A K E c hc p R N Ω D κ hκR hproj hT
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hnorm : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hsplit⟩ := GlobalTheory.T.hodge_tate_chart_different_bound A K hAK E c hc p R N Ω D κ σ d m hnorm hd hdiv h1.2 hP2
  have hq := GlobalTheory.T.hodge_tate_chart_divisibility A K hAK E c hc p R N Ω D κ σ m (hnorm σ) hdiv h1.2
  have hq' := GlobalTheory.T.hodge_tate_chart_divisibility A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hnorm _) hdiv h1.2
  have hcomp := GlobalTheory.T.hodge_tate_chart_dual_pairing A K E c hc p R N Ω D κ σ d d' m i hdiv hd hd' h1.2 hP1 hP2 hT hi
  refine ⟨i, hi, hsplit i hi, fun x => ⟨?_, ?_⟩, hq.2.2⟩
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu'⟩ := hu.pow m
      refine ⟨0, ((u⁻¹ : Aˣ) : A) • x, ?_⟩
      rw [map_zero, zero_add, ← hu', smul_smul, Units.mul_inv, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hq.2.1
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) := Module.Finite.iff_fg.2 hq'.2.1
      haveI := hP1
      haveI := hP2
      have hrank := GlobalTheory.T.hodge_tate_chart_non_unit_p A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 hT
      rw [← finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom))] at hrank
      obtain ⟨r, hr⟩ := hsplit i hi
      let qL : (Fin N → A) →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ) (qLin D σ) hq.1
      refine GlobalTheory.T.projective_split_modulo_element A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m)
        i r qL (by rw [add_comm]; exact hrank) hr ?_ ?_ x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, y', hy', e⟩ := hq.2.2 y hy
        exact ⟨x, ⟨y', hy'⟩, Subtype.ext e⟩
      · intro w
        obtain ⟨y, hy, e⟩ := hcomp w
        exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y, hy, hy'⟩ := hcomp w
    refine ⟨y + D.q σ x', add_mem hy (hq.1 x'), ?_⟩
    have e1 := (qLin D σ).map_add (i w) (((p : A) ^ m) • x')
    have e2 := (qLin D σ).map_smul ((p : A) ^ m) x'
    change D.q σ _ = _
    change (qLin D σ) _ = _
    rw [e1, e2]
    change D.q σ (i w) + _ = _
    rw [hy', smul_add]
    rfl

end GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence
