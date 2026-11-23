import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConnectionLinearInSection

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

open GlobalTheory.NabLinear in

theorem nab_smul_secN {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) (F F' : SecN Xo y.x k) (r : S)
    (hF : ∀ j, F'.f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S r) * F.f j) :
    ∀ α, nab y (k : ℤ) F' α = r * nab y (k : ℤ) F α := by
  intro α
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨C, hex, hval⟩ := hnab.2 S y
  obtain ⟨f, hf⟩ := hex k F
  have hf' : IsGerm y C.d C.x C.B.A.act C.e C.wP k F' (MvPowerSeries.C r * f) := by
    unfold IsGerm at hf ⊢
    intro m
    obtain ⟨F₁, τ, h1, hc, hv⟩ := hf m
    obtain ⟨F₂, h2⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ)
      (jBase y C.d m 1 ▷ Xo.univ.t.G) (whiskerRight_snd _ _) F'
    refine ⟨F₂, τ, h2, hc, ?_⟩
    have hs := GlobalTheory.NabLinear.isValueAt_scale Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (jBase y C.d m 1) hF h1 h2 hv
    convert hs using 1
    have hj : (jBase y C.d m 1).left = spMap (algebraMap S (Jet S (Fin 1 × Fin C.d) m)) := rfl
    rw [hj, GlobalTheory.NabLinear.appTop_toΓ, ← map_mul, ← GlobalTheory.NabLinear.psJet_C]
    congr 1
    clear hval hex hs h1 h2 hv hc hF hnab hj F₁ F₂ hf
    unfold psJet
    rw [← map_mul]
    congr 1
    unfold psTrunc
    have h0 : (0 : Fin 1 × Fin C.d →₀ ℕ) ∈ degLE m := by
      unfold degLE
      simp
      exact ⟨fun _ => 0, by ext; simp⟩
    have hC : ∑ e ∈ degLE m, MvPolynomial.monomial e
        (MvPowerSeries.coeff e (MvPowerSeries.C r : MvPowerSeries (Fin 1 × Fin C.d) S)) =
        MvPolynomial.monomial 0 r := by
      rw [Finset.sum_eq_single_of_mem 0 h0 (fun e _ he => by rw [MvPowerSeries.coeff_C, if_neg he, map_zero]),
        MvPowerSeries.coeff_C, if_pos rfl]
    rw [hC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPolynomial.monomial_mul, zero_add]
  exact (hval k F' _ hf' α).trans ((GlobalTheory.NabLinear.nabVal_C_mul C.B C.h H.w0 k r f C.uvec _).trans
    (congrArg (r * ·) (hval k F f hf α).symm))

theorem sum_support_C_mul {σ K S : Type} [CommRing K] [CommRing S] [Algebra K S] (P : MvPolynomial σ K) (s : K)
    (g : (σ →₀ ℕ) → S) :
    ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m =
      algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
  classical
  have hsub : (MvPolynomial.C s * P).support ⊆ P.support := by
    rw [MvPolynomial.C_mul']
    exact MvPolynomial.support_smul
  calc ∑ m ∈ (MvPolynomial.C s * P).support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m
      = ∑ m ∈ P.support, algebraMap K S ((MvPolynomial.C s * P).coeff m) * g m := by
        apply Finset.sum_subset hsub
        intro m _ hm
        rw [MvPolynomial.mem_support_iff, not_not] at hm
        rw [hm, map_zero, zero_mul]
    _ = algebraMap K S s * ∑ m ∈ P.support, algebraMap K S (P.coeff m) * g m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [MvPolynomial.coeff_C_mul, map_mul, _root_.mul_assoc]

theorem hv_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), (∀ (k : ℕ) (F F' : Fin n → SecN Xo y.x k) (r : Fin n → S), (∀ b j, (F' b).f j = liftFun Xo.univ.t.G _ (T := ptO Xo y.x) (toΓ S (r b)) * (F b).f j) → hv Xo c nab y k F' P = (∏ b, r b) * hv Xo c nab y k F P) ∧ (∀ (k : ℕ) (F : Fin n → SecN Xo y.x k) (s : c.F), hv Xo c nab y k F (MvPolynomial.C s * P) = algebraMap c.F S s * hv Xo c nab y k F P) ∧ ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b) = hv Xo c nab y (N ^ 2) (fun b => sqN Xo N (F b)) P := by
  intro E _ _ _ H Dw l Xo c _ _ nab hnab S _ _ y n P
  refine ⟨?_, ?_, ?_⟩
  · intro k F F' r hF
    unfold hv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have key : ∀ b, nab y (k : ℤ) (F' b) (colOf m b) = r b * nab y (k : ℤ) (F b) (colOf m b) :=
      fun b => nab_smul_secN Xo c nab hnab y k (F b) (F' b) (r b) (hF b) _
    simp only [key, Finset.prod_mul_distrib]
    ring
  · intro k F s
    unfold hv
    exact sum_support_C_mul P s _
  · intro N F
    unfold hv sqN
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1

end GlobalTheory.PlaceInt
