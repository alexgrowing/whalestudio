import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

variable {R : Type} [CommRing R]

theorem coeff_eq_of_psJet {ι : Type} [Fintype ι] [DecidableEq ι] {D : ℕ} {a b : MvPowerSeries ι R}
    (h : psJet D a = psJet D b) {e : ι →₀ ℕ} (he : e.degree ≤ D) :
    MvPowerSeries.coeff e a = MvPowerSeries.coeff e b := by
  have h' : Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D a) =
      Ideal.Quotient.mk (orig R ι ^ (D + 1)) (psTrunc D b) := h
  have hm := Ideal.Quotient.eq.mp h'
  have h0 := coeff_eq_zero_of_mem hm (show e.degree < D + 1 by omega)
  rw [MvPolynomial.coeff_sub, coeff_psTrunc D a e he, coeff_psTrunc D b e he] at h0
  exact sub_eq_zero.mp h0

theorem psJet_subst_congr {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (D : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f g : MvPowerSeries σ R}
    (h : psJet D f = psJet D g) : psJet D (MvPowerSeries.subst a f) = psJet D (MvPowerSeries.subst a g) := by
  rw [psJet_subst D a ha f, psJet_subst D a ha g, h]

def psJetM {ι : Type} [Fintype ι] [DecidableEq ι] (D : ℕ) : MvPowerSeries ι R →* Jet R ι D where
  toFun := psJet D
  map_one' := psJet_one D
  map_mul' := psJet_mul D

theorem psJet_prod_congr {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b

theorem cc_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {g : MvPowerSeries σ R}
    (hg : MvPowerSeries.constantCoeff g = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) = 0 := MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) ha hg

theorem subst_exp {σ τ : Type} [Finite σ] [Algebra ℚ R] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (g : MvPowerSeries σ R)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst a (PowerSeries.subst g (PowerSeries.exp R)) =
      PowerSeries.subst (MvPowerSeries.subst a g) (PowerSeries.exp R) := by
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.subst_exp a ha hg

theorem prod_exp {τ : Type} [Algebra ℚ R] : ∀ (n : ℕ) (q : Fin n → MvPowerSeries τ R),
    (∀ b, MvPowerSeries.constantCoeff (q b) = 0) →
    ∏ b, PowerSeries.subst (q b) (PowerSeries.exp R) = PowerSeries.subst (∑ b, q b) (PowerSeries.exp R)
  | 0, q, _ => by rw [Fin.prod_univ_zero, Fin.sum_univ_zero, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  | n + 1, q, hq => by
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, prod_exp n (fun b => q b.succ) (fun b => hq _),
      ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add (ha := hq 0)
        (hb := by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hq _)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
