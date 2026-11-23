import Mathlib
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q MeasureTheory

namespace GlobalTheory

theorem haarOn_UW_eq_of_mass_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μ ν : Measure (Mt k r))
    (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) (hν : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) ν)
    (h1 : μ Set.univ = 1) (h2 : ν Set.univ = 1) : ν = μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ ν (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hμ hν.conc hν.left hν.finite_compact
  have h3 := congrArg (fun m : Measure (Mt k r) => m Set.univ) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h1, h2, mul_one] at h3
  have h4 : c = 1 := by exact_mod_cast h3.symm
  rw [hc, h4, one_smul]

theorem unitaryMeasureDatum_productMeasure_eq_of_same_vectors : ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (k r : ℕ) (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (D' : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq'), D'.z = D.z → D'.z' = D.z' → D.μW Set.univ = 1 → D.μW' Set.univ = 1 → D'.μW Set.univ = 1 → D'.μW' Set.univ = 1 → D'.μN = D.μN → D'.μSS = D.μSS := by
  intro Wp _ _ _ Wq _ _ _ Wq' _ _ _ k r D D' hz hz' h1 h2 h3 h4 hN
  have e1 : D'.μW = D.μW := haarOn_UW_eq_of_mass_one D.z _ _ D.haarW (hz ▸ D'.haarW) h1 h3
  have e2 : D'.μW' = D.μW' := haarOn_UW_eq_of_mass_one D.z' _ _ D.haarW' (hz' ▸ D'.haarW') h2 h4
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS
  rw [e1, e2, hN]

end GlobalTheory
