import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRuleStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem hv_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  intro E _ _ _ H Dw l Xo c inst hstar nab hnab S _ _ y a N k k' haN hk n F F' hF w P hP
  have e : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star _ _ (fun x => (hstar x).trans rfl)
  subst e

  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 c.F)) P.support
    (fun m => P.coeff m)
  have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hbM ((IsFractionRing.injective (𝓞 c.F) c.F) (by rw [h0, map_zero]))

  have hsmul : ∀ (k0 : ℕ) (G : Fin n → SecN Xo y.x k0),
      hv Xo c nab y k0 G (algebraMap (𝓞 c.F) c.F b • P) =
        algebraMap c.F S (algebraMap (𝓞 c.F) c.F b) * hv Xo c nab y k0 G P := by
    intro k0 G
    unfold hv
    rw [MvPolynomial.support_smul_eq hb0, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

  have hQ : algebraMap (𝓞 c.F) c.F b • P ∈ harmA c w n := by
    unfold HH HHa at hP
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨⟨Submodule.smul_mem _ _ h1, fun σ i i' hi t => by rw [map_smul, h2 σ i i' hi t],
      fun m hm σ i => h3 m (MvPolynomial.support_smul hm) σ i⟩, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · obtain ⟨r, hr⟩ := hb m hm
      have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F b * P.coeff m := by
        rw [hr, Algebra.smul_def]
      rw [← hr']
      exact r.2
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      exact Subring.zero_mem _
  have key : hv Xo c nab y k' F' (algebraMap (𝓞 c.F) c.F b • P) =
      algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F (algebraMap (𝓞 c.F) c.F b • P) :=
    GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab S y a N k (k' : ℤ) (by rw [hstar]; exact haN)
      (by exact_mod_cast hk) n F F' (fun i => hF i) w _ hQ
  rw [hsmul, hsmul, _root_.mul_left_comm] at key
  exact mul_left_cancel₀ ((map_ne_zero _).mpr hb0) key
end GlobalTheory.PlaceInt
