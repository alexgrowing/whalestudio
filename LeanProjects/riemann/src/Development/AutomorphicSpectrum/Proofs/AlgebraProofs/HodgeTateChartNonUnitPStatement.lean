import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitP
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_non_unit_p : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj | exact GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj <;> assumption)
