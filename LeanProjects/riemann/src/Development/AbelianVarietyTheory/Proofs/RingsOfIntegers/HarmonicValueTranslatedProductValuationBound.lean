import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScaleStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralPointEqValueOnBiextensionCoStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.TermBound

theorem totalDegree_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : RowDeg r n k a P) (h0 : P ≠ 0) :
    P.totalDegree = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
  have hH : P.IsHomogeneous (∑ σ : T, ∑ i : Fin (r σ), a σ i) := by
    intro m hm
    have hm' : m ∈ P.support := by simpa [MvPolynomial.mem_support_iff] using hm
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => by simpa using hP m hm' σ i
  exact hH.totalDegree h0

section Num
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem nrm_mul' (Dw : Datum H) (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (α β : 𝓞 E) :
    nrm Dw c w (α * β) = nrm Dw c w α * nrm Dw c w β := by
  simp only [nrm, map_mul, mul_pow, Finset.prod_mul_distrib]

theorem nrm_natCast' (Dw : Datum H) (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (m : ℕ) :
    nrm Dw c w (m : 𝓞 E) = (m : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), w (τ, i)) := by
  simp only [nrm, map_natCast, Finset.prod_pow_eq_pow_sum]
end Num

theorem nval_inv_pow_mul (T : CDVR) (e m d : ℕ) (hm : IsUnit (m : T.V)) (x : T.Fr) :
    nval T.V e ((((m : T.Fr)) ^ d)⁻¹ * x) = nval T.V e x := by
  have hv1 : valV T.V ((m : T.Fr)) = 1 := by
    obtain ⟨u, hu⟩ := hm
    have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) ≤ 1 := by
      unfold valV
      apply IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    have h2 : valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) ≤ 1 := by
      unfold valV
      apply IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    have h3 : valV T.V (algebraMap T.V T.Fr (u : T.V)) *
        valV T.V (algebraMap T.V T.Fr ((u⁻¹ : T.Vˣ) : T.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hcast : (m : T.Fr) = algebraMap T.V T.Fr (u : T.V) := by rw [hu, map_natCast]
    rw [hcast]
    refine le_antisymm h1 ?_
    calc (1 : _) = _ := h3.symm
      _ ≤ valV T.V (algebraMap T.V T.Fr (u : T.V)) * 1 := by gcongr
      _ = _ := mul_one _
  have hv : valV T.V ((m : T.Fr) ^ d)⁻¹ = 1 := by
    rw [map_inv₀, map_pow, hv1, one_pow, inv_one]
  have hne : ((m : T.Fr) ^ d)⁻¹ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  unfold nval vV
  rw [map_mul, hv, _root_.one_mul]
  by_cases hx : x = 0
  · rw [if_pos (by rw [hx, mul_zero]), if_pos hx]
  · rw [if_neg (mul_ne_zero hne hx), if_neg hx]

theorem term_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → IsUnit (n' : T.V) → ∀ (x₁ x₂ : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ b, x₁ b ^ (N ^ 2) = 1 ∧ x₂ b ^ (N ^ 2) = 1 ∧ (x₁ b ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 ∧ (x₂ b ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 ∧ IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (x₁ b) (x₂ b) (F b)) → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ HH c w n → MvPolynomial.map io P ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) * hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hC nab hnab e ρ w n he hCB N n' A Bn α β hN hNe hA hBn hn' x₁ x₂ F hx P hP hPF
  letI : Algebra c.F T.Fr := io.toAlgebra
  have hbN : H.bar (N : 𝓞 E) = N := by rw [← hstar, star_natCast]
  have hbar : H.bar (N : 𝓞 E) = H.bar β * H.bar α * n' := by
    rw [← hstar, hNe, star_mul', star_mul', star_natCast, hstar, hstar]
  have hN2' : (N : 𝓞 E) ^ 2 = (n' : 𝓞 E) ^ 2 * A * Bn := by
    linear_combination (-(N : 𝓞 E)) * hbN + H.bar (N : 𝓞 E) * hNe + (β * α * n') * hbar +
      ((n' : 𝓞 E) ^ 2 * β * H.bar β) * hA + ((n' : 𝓞 E) ^ 2 * A) * hBn
  have hN2 : N ^ 2 = n' ^ 2 * A * Bn := by exact_mod_cast hN2'
  have h45 := fun b => GlobalTheory.T.mixed_translate_pullback_eq_reached_section E H Dw l Xo T.Fr (xOf y) N n' A Bn α β hN hNe hA hBn (sOf1 y)
    (x₁ b) (x₂ b) (F b) (hx b).1 (hx b).2.1 (hx b).2.2.1 (hx b).2.2.2.1 (hx b).2.2.2.2
  choose hh hReach hPull using fun b => (h45 b).2
  have hReg := fun b => GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hstar T io y C hC (n' ^ 2 * A) (hh b) (hReach b)
  choose f hf using fun b =>
    (GlobalTheory.T.regular_section_integral_germ_unique_scale E H Dw l Xo c hstar T io y C hC.1 (n' ^ 2 * A) (hh b)).1 (hReg b)
  obtain ⟨B, hB, h49⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hstar T io y C
  have h48 := GlobalTheory.T.harmonicValue_integralPoint_eq_value_on_biextensionCopies E H Dw l Xo c hstar T io y C nab hnab B hB (n' ^ 2 * A) n hh f hf w P hP
  have h58 := GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hstar nab hnab T.Fr y.1 β Bn (n' ^ 2 * A) (N ^ 2) hBn hN2 n hh
    (fun b => sqN Xo N (F b)) hPull w P hP
  by_cases hP0 : P = 0
  · subst hP0
    have h0 : hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) (0 : MvPolynomial (LtN Dw n) c.F) = 0 := by
      simp [hv]
    rw [h0, mul_zero]
    unfold nval
    simp
  · have hRow : RowDeg Dw.mult n c.F (fun τ i => w (τ, i)) P := by
      unfold HH HHa at hP
      exact hP.2.2
    have hdeg := totalDegree_of_rowDeg Dw.mult n c.F (fun τ i => w (τ, i)) P hRow hP0
    beta_reduce at hdeg
    have hNn := nrm_natCast' Dw c w N
    rw [hNe, nrm_mul', nrm_mul', nrm_natCast', ← hdeg] at hNn
    have hc : nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹ * nrm Dw c w β =
        ((n' : c.F) ^ P.totalDegree)⁻¹ := by
      have hN0 : ((N : c.F) ^ P.totalDegree) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.pos.ne')
      rw [← hNn] at hN0 ⊢
      have ha : nrm Dw c w α ≠ 0 := fun h => hN0 (by simp [h])
      have hb : nrm Dw c w β ≠ 0 := fun h => hN0 (by simp [h])
      have hn : ((n' : c.F) ^ P.totalDegree) ≠ 0 := fun h => hN0 (by simp [h])
      field_simp
    have hval : io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
        hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F b)) P =
        ((n' : T.Fr) ^ P.totalDegree)⁻¹ * hv Xo c nab y.1 (n' ^ 2 * A) hh P := by
      rw [h58, RingHom.algebraMap_toAlgebra, ← _root_.mul_assoc, ← map_mul, hc, map_inv₀, map_pow, map_natCast]
    rw [hval, nval_inv_pow_mul T e n' P.totalDegree hn', h48]
    exact (h49 B hB).2.2.2 e ρ w n hCB (n' ^ 2 * A) (MvPolynomial.map io P) hPF _

end GlobalTheory.PlaceInt.TermBound
