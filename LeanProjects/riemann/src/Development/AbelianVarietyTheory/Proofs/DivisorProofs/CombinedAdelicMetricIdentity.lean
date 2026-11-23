import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeightSmoothNormalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescalingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverComb

theorem approx : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (M : Adl (cxSt F) Y) (ι : Type) [Fintype ι] (ρ : ι → Adl (cxSt F) Y) (g : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (q : ℕ) (b : ι → ℤ), 0 < q → q • M.D = ∑ i, b i • (ρ i).D → (∀ σ z, PosAt (M.m σ) z ∧ q * lnAdl M σ z = Real.log ‖ratVal (genAt M.D (under z) ^ q / ∏ i, genAt (ρ i).D (under z) ^ b i) z‖ + ∑ i, b i * lnAdl (ρ i) σ z - q * (M.n : ℕ) * g σ z) → (∀ v e y, q * M.lg v e y = Real.log (e.w (valAt y.1 (genAt M.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) + ∑ i, b i * (ρ i).lg v e y) → ∀ (K : ℕ) (e : ι → ℤ) (n : ι → ℤ), (∀ i, n i * e i = K * b i) → ∀ (L : ι → HermLB V.p), (∀ i, Norms V (L i) (fun x => genAt (ρ i).D x ^ e i) (fun σ y => e i * lnAdl (ρ i) σ y) (fun v e' y => e i * (ρ i).lg v e' y)) → ∀ (u : ∀ σ : 𝓞 F →+* ℂ, CxPts V.p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))), (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F))), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → u _ y' = 2 * g σ y) → Norms V (ArInt.comb (fun o : Option ι => o.elim (ArInt.fnB u hu hc) L) (fun o => o.elim (((K * q * (M.n : ℕ) : ℕ) : ℤ)) n)) (fun x => genAt M.D x ^ (K * q)) (fun σ y => ((K * q : ℕ) : ℝ) * lnAdl M σ y) (fun v e y => ((K * q : ℕ) : ℝ) * M.lg v e y) := by
  intro F _ _ Y V M ι _ ρ g q b hq hD hinf hfin K e n hne L hL u hu hc hug
  classical
  have h0 : Norms V (ArInt.fnB u hu hc) (fun _ => 1) (fun σ y => -g σ y) (fun _ _ _ => 0) :=
    (GlobalTheory.T.conjugate_weight_smooth_normalization F Y V).2 u hu hc _ (fun σ z y y' e₁ e₂ => by rw [hug σ z y y' e₁ e₂]; ring)
  have hall : ∀ o : Option ι, Norms V (o.elim (ArInt.fnB u hu hc) L)
      (o.elim (fun _ => 1) (fun i x => genAt (ρ i).D x ^ e i))
      (o.elim (fun σ y => -g σ y) (fun i σ y => (e i : ℝ) * lnAdl (ρ i) σ y))
      (o.elim (fun _ _ _ => 0) (fun i v w y => (e i : ℝ) * (ρ i).lg v w y)) := by
    rintro (_ | i)
    · exact h0
    · exact hL i
  have hC := norms_comb hall (fun o => o.elim (((K * q * (M.n : ℕ) : ℕ) : ℤ)) n)
  have hu0 : ∀ x, UnitAt x (genAt M.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) := by
    intro x
    have h₁ := (Base.isEqn_eqn M.D x).nsmul q
    have h₂ : (∑ i, b i • (ρ i).D).IsEqn x (∏ i, eqn (ρ i).D x ^ b i) := by
      have key : ∀ s : Finset ι, (∑ i ∈ s, b i • (ρ i).D).IsEqn x (∏ i ∈ s, eqn (ρ i).D x ^ b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using CartierDiv.isEqn_zero x
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.prod_insert hj]
          exact ((Base.isEqn_eqn (ρ j).D x).zsmul (b j)).add ih
      exact key _
    rw [hD] at h₁
    have h₃ := h₁.iff_unitAt.1 h₂
    convert h₃ using 1
    simp only [genAt, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.coe_prod, inv_pow, inv_zpow', Finset.prod_inv_distrib]
    simp only [zpow_neg, Finset.prod_inv_distrib, div_inv_eq_mul]
    rw [mul_comm, div_eq_mul_inv]
  have hP : ∀ x, (∏ i, genAt (ρ i).D x ^ b i) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  have hsum : ∀ w : ι → ℝ, ∑ i, (n i : ℝ) * ((e i : ℝ) * w i) = K * ∑ i, (b i : ℝ) * w i := by
    intro w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (n i : ℝ) * e i = K * b i := by exact_mod_cast hne i
    linear_combination w i * this
  have h2 := GlobalTheory.T.norms_unit_rescaling F Y V _ _ _ _ (fun x => (genAt M.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) ^ K)
    (fun x => InducedPow.unitAt_pow (hu0 x) K) hC
  refine h2.congr (fun x => ?_) (fun σ y => ?_) (fun v w y => ?_)
  · simp only [Fintype.prod_option, Option.elim, one_zpow, one_mul]
    have hp : ∀ i, (genAt (ρ i).D x ^ e i) ^ n i = (genAt (ρ i).D x ^ b i) ^ K := fun i => by
      rw [← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm (e i), hne i, mul_comm]
    simp only [hp, Finset.prod_pow, ← mul_pow, div_mul_cancel₀ _ (hP x), ← pow_mul, mul_comm q K]
  · simp only [Fintype.sum_option, Option.elim]
    rw [hsum, InducedPow.ratVal_pow _ (hu0 _) K, norm_pow, Real.log_pow]
    have H := (hinf σ y).2
    generalize Real.log ‖ratVal (genAt M.D (under y) ^ q / ∏ i, genAt (ρ i).D (under y) ^ b i) y‖ = A at H ⊢
    push_cast
    linear_combination -(K : ℝ) * H
  · simp only [Fintype.sum_option, Option.elim]
    rw [hsum, InducedPow.valAt_pow _ (hu0 _).regAt K, map_pow, Real.log_pow]
    have H := hfin v w y
    generalize Real.log (w.w (TrueGeo.valAt y.1 (genAt M.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) = A at H ⊢
    push_cast
    linear_combination -(K : ℝ) * H

end GlobalTheory.CoverComb
