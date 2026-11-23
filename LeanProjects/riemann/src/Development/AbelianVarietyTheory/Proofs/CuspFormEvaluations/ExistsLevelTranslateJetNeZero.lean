import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockHxDifferentiable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem polyDeriv_const_mul_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {G : W → ℂ} (hG : Differentiable ℂ G) (x : W) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  have := I2.polyDeriv_sum P u (Finset.univ : Finset Unit) (fun _ => c) (fun _ => G)
    (fun _ _ k => I2.contDiff_of_differentiable_fd hG k) x
  simpa using this

theorem polyDeriv_const_mul_of_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {T : W → ℂ}
    (hG : Differentiable ℂ fun z => c * T z) (x : W) :
    I2.polyDeriv P u (fun z => c * T z) x = c * I2.polyDeriv P u T x := by
  by_cases hc : c = 0
  · have := polyDeriv_const_mul_entire P u 0 hG x
    simpa [hc] using this
  · have h : T = fun z => c⁻¹ * (c * T z) := by
      funext z; field_simp
    conv_rhs => rw [h]
    rw [polyDeriv_const_mul_entire P u c⁻¹ hG x]
    field_simp

theorem exists_level_translate_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv θ κ hθ hm hκ P hP hdeg
  obtain ⟨F, hF, hFa, hFP⟩ := GlobalTheory.T.exists_theta_sublattice_jet_ne_zero_alt E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 P hP hdeg
  obtain ⟨s, cf, hs', hsum⟩ := GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv
    θ κ hθ hm hκ F hF hFa
  obtain ⟨hcomp, -, -, hdiff, hprod⟩ := fock_laws E r X g bas idx n hs hn x hd 1 θ
  have hprod' := hprod (fun _ => θ) κ v hv.1 hκ
  have hent : ∀ y : Matrix (Fin n) (Fin r) E,
      Differentiable ℂ fun z => κ * thA X bas idx (heisG X bas y v) x z := by
    intro y
    have : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
        fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (y b)) θ (z b) :=
      funext fun z => (hprod' y z).symm
    rw [this]
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin g → ℂ =>
        fock X bas idx x 1 (pv X idx x (y b)) θ (z b) := fun b =>
      (hdiff hθ.1 (pv X idx x (y b))).comp (f := fun z : Fin n → Fin g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finset_prod (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  have hFe : F = fun z => ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := funext hsum
  rw [hFe, I2.polyDeriv_sum P _ s cf (fun y z => κ * thA X bas idx (heisG X bas y v) x z)
    (fun y _ k => I2.contDiff_of_differentiable_fd (hent y) k)] at hFP
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFP
  refine ⟨y, hs' y hy, fun y' hy' => ?_⟩
  have hne' := right_ne_zero_of_mul hne
  have hrow : ∀ b, ∃ c : ℂ, fock X bas idx x 1 (pv X idx x (y b)) θ =
      c • fock X bas idx x 1 (pv X idx x (y' b)) θ := by
    intro b
    have h1 := hθ.2 _ (hy' b)
    have h2 := hcomp (pv X idx x (y b)) (pv X idx x (y' b - y b))
    have h3 : pv X idx x (y b) + pv X idx x (y' b - y b) = pv X idx x (y' b) := by
      funext j
      have := congrFun (per_add X x (y b) (y' b - y b)) (idx j)
      rw [add_sub_cancel] at this
      exact this.symm
    rw [h3] at h2
    have h4 : ∀ (e : ℂ) (a : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ),
        fock X bas idx x 1 a (e • φ) = e • fock X bas idx x 1 a φ := by
      intro e a φ
      funext z
      simp only [fock, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨_, by conv_lhs => rw [← h1, h4, h2, smul_smul]⟩
  choose c hcc using hrow
  have hfun : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
      fun z => (∏ b, c b) * (κ * thA X bas idx (heisG X bas y' v) x z) := by
    funext z
    rw [← hprod' y z, ← hprod' y' z, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [hcc b]; rfl
  rw [hfun, polyDeriv_const_mul_entire P _ _ (hent y'), polyDeriv_const_mul_of_entire P _ _ (hent y')] at hne'
  exact right_ne_zero_of_mul hne'

end GlobalTheory.Dict
