import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr

set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.PowGerm

theorem nabValN_eq_zero_of_coeff_eq_zero :
    ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u f P hf
  classical
  unfold nabValN
  rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hdeg : a.degree ≤ P.totalDegree := by
    have := MvPolynomial.le_totalDegree ha
    rwa [Finsupp.degree_apply]
  rw [NabJet.constantCoeff_DmonN_congr _ cp u a _ 0 fun mo hmo => ?_,
    (NabJet.isLinearMap_DmonN (B.FK K) cp u a).map_zero, map_zero, mul_zero]
  rw [NabJet.coeff_mul_congr P.totalDegree f 0 _ (fun b hb => by rw [hf b hb, map_zero]) mo (hmo.trans hdeg), zero_mul]

end GlobalTheory.PowGerm
